import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

// mend: applies AI-written edits in unified diff, SEARCH/REPLACE, V4A, and JSON formats.
// Spec: SPEC.md. Node 22 stdlib only. Keep trial handover at bottom.

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'] as const;
type Format = typeof FORMATS[number];
class Exit2 extends Error { line: string; constructor(line: string) { super(line); this.line = line; } }
class Fail extends Error { code: string; path: string; constructor(code: string, path: string) { super(code); this.code = code; this.path = path; } }

type NL = '\n' | '\r\n';
type FileState = { text: string; nl: NL; final: boolean } | null;
type Edit = (tree: Tree) => void;

const blank = (s: string): boolean => s.trim() === '';
function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}
function isSafePath(p: string): boolean {
  if (p === '' || p.startsWith('/') || p.includes('\\')) return false;
  return p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}
function readFileState(p: string): FileState {
  let st: ReturnType<typeof statSync>;
  try { st = statSync(p); } catch { return null; }
  if (!st.isFile()) return null;
  const text = readFileSync(p, 'utf8');
  const i = text.indexOf('\n');
  const nl: NL = i > 0 && text[i - 1] === '\r' ? '\r\n' : '\n';
  const final = text !== '' && (nl === '\r\n' ? text.endsWith('\r\n') : text.endsWith('\n'));
  return { text, nl, final };
}
function splitFileLines(text: string, nl: NL, final: boolean): string[] {
  if (text === '') return [];
  const parts = text.split(nl);
  if (final) parts.pop();
  return parts;
}
function joinFileLines(lines: string[], nl: NL, final: boolean): string {
  if (lines.length === 0) return '';
  return lines.join(nl) + (final ? nl : '');
}
class Tree {
  private orig = new Map<string, FileState>();
  now = new Map<string, FileState>();
  moves: [string,string][] = [];
  original(p: string): FileState { if (!this.orig.has(p)) this.orig.set(p, readFileState(p)); return this.orig.get(p)!; }
  get(p: string): FileState { return this.now.has(p) ? this.now.get(p)! : this.original(p); }
  set(p: string, s: FileState): void { this.now.set(p, s); }
  snapshot(): {now:Map<string,FileState>; moves:[string,string][]} { return {now:new Map(this.now), moves:[...this.moves]}; }
  restore(snap: {now:Map<string,FileState>; moves:[string,string][]}): void { this.now.clear(); for (const [k,v] of snap.now) this.now.set(k,v); this.moves=[...snap.moves]; }
  recordMove(oldP:string,newP:string){ this.moves.push([oldP,newP]); }
}
function ensureSafe(p: string): void { if (!isSafePath(p)) throw new Fail('unsafe', p); }
function ensureExists(tree: Tree, p: string): { text: string; nl: NL; final: boolean } {
  ensureSafe(p); const s = tree.get(p); if (s === null) throw new Fail('missing', p); return s;
}

function detect(lines: string[]): Format | null {
  let first = -1;
  for (let i = 0; i < lines.length; i++) { if (!blank(lines[i]!)) { first = i; break; } }
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c0 = lines[first]!.trimStart()[0];
  if (c0 === '[' || c0 === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

function normTier(line: string, tier: 0 | 1 | 2): string {
  if (tier === 0) return line;
  if (tier === 1) return line.replace(/[ \t]+$/, '');
  return line.trim();
}
function findOccurrences(fileLines: string[], O: string[], tier: 0 | 1 | 2): number[] {
  if (O.length === 0) return []; // caller handles empty-old specially
  const occ: number[] = [];
  const max = fileLines.length - O.length;
  outer: for (let i = 0; i <= max; i++) {
    for (let j = 0; j < O.length; j++) if (normTier(fileLines[i + j]!, tier) !== normTier(O[j]!, tier)) continue outer;
    occ.push(i);
  }
  return occ;
}
function chooseTier(fileLines: string[], O: string[], strict: boolean): { tier: 0 | 1 | 2; occ: number[] } | null {
  const tiers: (0 | 1 | 2)[] = strict ? [0] : [0, 1, 2];
  for (const t of tiers) { const occ = findOccurrences(fileLines, O, t); if (occ.length > 0) return { tier: t, occ }; }
  return null;
}
function leadingWS(s: string): string { const m = s.match(/^[ \t]*/); return m ? m[0] : ''; }
function buildReplacement(fileMatched: string[], O: string[], N: string[], nIsCtx: boolean[], tier: 0 | 1 | 2): string[] {
  const ctxMap = new Map<number, string>();
  let oi = 0;
  for (let ni = 0; ni < N.length; ni++) {
    if (!nIsCtx[ni]) continue;
    let best = -1;
    if (tier === 2) {
      let bestTier = 3;
      for (let j = oi; j < O.length; j++) {
        let mt = 3;
        if (normTier(O[j]!, 0) === normTier(N[ni]!, 0)) mt = 0;
        else if (normTier(O[j]!, 1) === normTier(N[ni]!, 1)) mt = 1;
        else if (normTier(O[j]!, 2) === normTier(N[ni]!, 2)) mt = 2;
        if (mt < bestTier) { bestTier = mt; best = j; if (mt === 0) break; }
      }
    } else {
      for (let j = oi; j < O.length; j++) { if (normTier(O[j]!, tier) === normTier(N[ni]!, tier)) { best = j; break; } }
    }
    if (best >= 0) { ctxMap.set(ni, fileMatched[best]!); oi = best + 1; }
    else ctxMap.set(ni, N[ni]!);
  }
  const F = leadingWS(fileMatched[0] ?? '');
  const P = leadingWS(O[0] ?? '');
  return N.map((line, i) => {
    if (nIsCtx[i]) return ctxMap.get(i) ?? line;
    if (tier === 2 && line !== '' && !/^[ \t]+$/.test(line)) { if (P === '') return F + line; if (line.startsWith(P)) return F + line.slice(P.length); }
    return line;
  });
}
function replaceAt(fileLines: string[], pos: number, olen: number, outN: string[]): string[] {
  return [...fileLines.slice(0, pos), ...outN, ...fileLines.slice(pos + olen)];
}

// --- JSON (section 9) ---
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>; const pth = o.path;
  if (typeof pth !== 'string') return null;
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => { ensureSafe(pth); if (tree.get(pth) !== null) throw new Fail('exists', pth); tree.set(pth, { text, nl: '\n', final: text.endsWith('\n') }); };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str; const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const st = ensureExists(tree, pth);
      const toLF = (x: string) => st.nl === '\r\n' ? x.replaceAll('\r\n', '\n') : x;
      const fromLF = (x: string) => st.nl === '\r\n' ? x.replaceAll('\n', '\r\n') : x;
      const t = toLF(st.text); const old = toLF(oldStr);
      let count = 0; for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count++;
      if (count === 0) throw new Fail('no-match', pth);
      if (count > 1) throw new Fail('ambiguous', pth);
      const at = t.indexOf(old);
      tree.set(pth, { text: fromLF(t.slice(0, at) + toLF(newStr) + t.slice(at + old.length)), nl: st.nl, final: st.final });
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line; const ins = patchLines(o.new_str);
    return (tree) => {
      const st = ensureExists(tree, pth);
      const lines = splitFileLines(st.text, st.nl, st.final);
      if (line < 0 || line > lines.length) throw new Fail('no-match', pth);
      lines.splice(line, 0, ...ins);
      tree.set(pth, { text: joinFileLines(lines, st.nl, st.final), nl: st.nl, final: st.final });
    };
  }
  return null;
}
function jsonEdits(text: string, lines: string[]): Edit[] {
  let first = -1; for (let i = 0; i < lines.length; i++) if (!blank(lines[i]!)) { first = i; break; }
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown; try { v = JSON.parse(text); } catch { throw new Exit2(`error: parse ${first + 1}`); }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) { const e = jsonEdit(x); if (e === null) throw new Exit2(`error: parse ${first + 1}`); edits.push(e); }
    return edits;
  }
  for (let i = 0; i < lines.length; i++) {
    const l = lines[i]!; if (blank(l)) continue;
    let e: Edit | null = null; try { e = jsonEdit(JSON.parse(l)); } catch { e = null; }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`); edits.push(e);
  }
  return edits;
}

// --- SEARCH/REPLACE (section 7) ---
function srEdits(lines: string[], strict: boolean): Edit[] {
  type B = { path: string; old: string[]; neu: string[]; line: number };
  const blocks: B[] = []; let i = 0;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() === '<<<<<<< SEARCH') {
      const sLine = i + 1;
      let prevReplace = -1;
      for (let k = blocks.length - 1; k >= 0; k--) { prevReplace = (blocks[k] as any)._r; break; }
      let pth = '';
      for (let j = i - 1; j > prevReplace; j--) {
        if (blank(lines[j]!)) continue;
        const t = lines[j]!.trim(); if (t.startsWith('```')) continue;
        pth = t; break;
      }
      if (pth === '' && blocks.length > 0) pth = blocks[blocks.length - 1]!.path;
      if (pth === '') throw new Exit2(`error: parse ${sLine}`);
      let j = i + 1; const old: string[] = [];
      while (j < lines.length && lines[j]!.trimEnd() !== '=======') { old.push(lines[j]!); j++; }
      if (j >= lines.length) throw new Exit2(`error: parse ${sLine}`);
      j++; const neu: string[] = [];
      while (j < lines.length && lines[j]!.trimEnd() !== '>>>>>>> REPLACE') { neu.push(lines[j]!); j++; }
      if (j >= lines.length) throw new Exit2(`error: parse ${sLine}`);
      const b: any = { path: pth, old, neu, line: sLine }; b._r = j; blocks.push(b); i = j + 1; continue;
    }
    i++;
  }
  if (blocks.length === 0) throw new Exit2('error: parse 1');
  return blocks.map((b) => (tree: Tree) => {
    ensureSafe(b.path);
    if (b.old.length === 0) {
      if (tree.get(b.path) !== null) throw new Fail('exists', b.path);
      const text = b.neu.length > 0 ? b.neu.join('\n') + '\n' : '';
      tree.set(b.path, { text, nl: '\n', final: b.neu.length > 0 }); return;
    }
    const st = tree.get(b.path); if (st === null) throw new Fail('missing', b.path);
    const f = splitFileLines(st.text, st.nl, st.final);
    const found = chooseTier(f, b.old, strict);
    if (!found) throw new Fail('no-match', b.path);
    if (found.occ.length > 1) throw new Fail('ambiguous', b.path);
    const pos = found.occ[0]!;
    const outN = buildReplacement(f.slice(pos, pos + b.old.length), b.old, b.neu, b.neu.map(() => false), found.tier);
    tree.set(b.path, { text: joinFileLines(replaceAt(f, pos, b.old.length, outN), st.nl, st.final), nl: st.nl, final: st.final });
  });
}

// --- V4A (section 8) ---
type VChunk = { anchor: string | null; eof: boolean; old: string[]; neu: string[]; nIsCtx: boolean[] };
function v4aEdits(lines: string[], strict: boolean): Edit[] {
  let first = -1, last = -1;
  for (let i = 0; i < lines.length; i++) if (!blank(lines[i]!)) { if (first < 0) first = i; last = i; }
  if (first < 0 || lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first < 0 ? 1 : first + 1}`);
  if (last < 0 || lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  type Sec = { kind: 'add' | 'delete' | 'update'; path: string; newPath?: string; addLines: string[]; chunks: VChunk[]; line: number };
  const secs: Sec[] = []; let cur: Sec | null = null; let ch: VChunk | null = null;
  const flush = () => { if (ch && cur) { cur.chunks.push(ch); ch = null; } };
  for (let i = first + 1; i < last; i++) {
    const raw = lines[i]!; const ln = i + 1; const t = raw.trim();
    if (t.startsWith('*** Add File: ')) { flush(); cur = { kind: 'add', path: t.slice(14).trim(), addLines: [], chunks: [], line: ln }; secs.push(cur); continue; }
    if (t.startsWith('*** Delete File: ')) { flush(); cur = { kind: 'delete', path: t.slice(17).trim(), addLines: [], chunks: [], line: ln }; secs.push(cur); continue; }
    if (t.startsWith('*** Update File: ')) { flush(); cur = { kind: 'update', path: t.slice(17).trim(), addLines: [], chunks: [], line: ln }; secs.push(cur); continue; }
    if (t === '*** End Patch') break;
    if (cur && cur.kind === 'update' && t.startsWith('*** Move to: ') && cur.chunks.length === 0 && !ch) { cur.newPath = t.slice(13).trim(); continue; }
    if (!cur) { if (blank(raw)) continue; throw new Exit2(`error: parse ${ln}`); }
    if (cur.kind === 'add') { if (raw.startsWith('+')) cur.addLines.push(raw.slice(1)); else if (raw === '') cur.addLines.push(''); else throw new Exit2(`error: parse ${ln}`); continue; }
    if (cur.kind === 'delete') { if (blank(raw)) continue; throw new Exit2(`error: parse ${ln}`); }
    if (t === '*** End of File') { if (ch) { ch.eof = true; flush(); } continue; }
    if (raw.startsWith('@@')) { flush(); const a = raw.slice(2).trim(); ch = { anchor: a === '' ? null : a, eof: false, old: [], neu: [], nIsCtx: [] }; continue; }
    if (raw.startsWith(' ') || raw.startsWith('-') || raw.startsWith('+') || raw === '') {
      if (!ch) ch = { anchor: null, eof: false, old: [], neu: [], nIsCtx: [] };
      const k = raw === '' ? ' ' : raw[0]!; const txt = raw === '' ? '' : raw.slice(1);
      if (k === ' ' || k === '-') ch.old.push(txt);
      if (k === ' ' || k === '+') { ch.neu.push(txt); ch.nIsCtx.push(k === ' '); }
      continue;
    }
    throw new Exit2(`error: parse ${ln}`);
  }
  flush();
  for (const s of secs) {
    if (s.kind === 'add') { while (s.addLines.length > 0 && s.addLines[s.addLines.length - 1] === '') s.addLines.pop(); }
    else for (const c of s.chunks) {
      while (c.old.length > 0 && c.neu.length > 0 && c.old[c.old.length - 1] === '' && c.neu[c.neu.length - 1] === '' && c.nIsCtx[c.nIsCtx.length - 1]) { c.old.pop(); c.neu.pop(); c.nIsCtx.pop(); }
    }
  }
  for (const s of secs) if (s.kind === 'update' && s.chunks.length === 0 && s.newPath === undefined) throw new Exit2(`error: parse ${s.line}`);
  return secs.map((s) => (tree: Tree) => {
    ensureSafe(s.path);
    if (s.kind === 'add') {
      if (tree.get(s.path) !== null) throw new Fail('exists', s.path);
      const text = s.addLines.length > 0 ? s.addLines.join('\n') + '\n' : '';
      tree.set(s.path, { text, nl: '\n', final: s.addLines.length > 0 }); return;
    }
    if (s.kind === 'delete') { if (tree.get(s.path) === null) throw new Fail('missing', s.path); tree.set(s.path, null); return; }
    const st = tree.get(s.path); if (st === null) throw new Fail('missing', s.path);
    if (s.newPath !== undefined) { ensureSafe(s.newPath); if (s.newPath !== s.path && tree.get(s.newPath) !== null) throw new Fail('exists', s.newPath); }
    let f = splitFileLines(st.text, st.nl, st.final); let cursor = 0;
    for (const c of s.chunks) {
      if (c.anchor !== null) {
        const found = chooseTier(f, [c.anchor], strict);
        if (!found) throw new Fail('no-match', s.path);
        const at = found.occ.find((x) => x >= cursor);
        if (at === undefined) throw new Fail('no-match', s.path);
        cursor = at + 1;
      }
      if (c.old.length === 0) {
        const pos = c.eof ? f.length : cursor;
        const outN = buildReplacement([], [], c.neu, c.nIsCtx, 0);
        f = replaceAt(f, pos, 0, outN); cursor = pos + outN.length; continue;
      }
      let O = c.old, Nn = c.neu, nIs = c.nIsCtx;
      let found = chooseTier(f, O, strict);
      // tolerate trailing empty context past EOF
      if (!found) {
        let o2=[...O], n2=[...Nn], ni2=[...nIs];
        while (o2.length>0 && n2.length>0 && o2[o2.length-1]==='' && n2[n2.length-1]==='' && ni2[ni2.length-1]) {
          const tryO=o2.slice(0,-1), tryN=n2.slice(0,-1), tryNi=ni2.slice(0,-1);
          const f2f=chooseTier(f,tryO.length?tryO:[''],strict);
          // only accept if tryO matches at EOF
          if (tryO.length===0) break;
          const ff=chooseTier(f,tryO,strict);
          if (ff) { const endPos=f.length-tryO.length; if (ff.occ.includes(endPos)) { o2=tryO; n2=tryN; ni2=tryNi; found=ff; break; } }
          o2=tryO; n2=tryN; ni2=tryNi;
        }
        if (!found) found = chooseTier(f, o2, strict);
        if (found) { O=o2; Nn=n2; nIs=ni2; }
      }
      if (!found) throw new Fail('no-match', s.path);
      let pos: number;
      if (c.eof) { const endPos = f.length - O.length; pos = found.occ.includes(endPos) ? endPos : -1; if (pos < 0) throw new Fail('no-match', s.path); }
      else {
        const after = found.occ.filter((x) => x >= cursor);
        if (after.length === 0) throw new Fail('no-match', s.path);
        pos = after[0]!;
      }
      const outN = buildReplacement(f.slice(pos, pos + O.length), O, Nn, nIs, found.tier);
      f = replaceAt(f, pos, O.length, outN); cursor = pos + outN.length;
    }
    const text = joinFileLines(f, st.nl, st.final);
    if (s.newPath !== undefined && s.newPath !== s.path) { tree.set(s.newPath, { text, nl: st.nl, final: st.final }); tree.set(s.path, null); tree.recordMove(s.path, s.newPath); }
    else tree.set(s.path, { text, nl: st.nl, final: st.final });
  });
}

// --- Unified diff (section 6) ---
type UFile = { path: string; delPath: string | null; newPath: string | null; created: boolean; deleted: boolean; oldLines: string[] | null; hunks: { oldStart: number; oldCount: number; lines: string[] }[]; line: number };
function stripA(path: string): string {
  const m = path.match(/^[ab]\/(.+)$/); if (m) return m[1]!;
  if (path === '/dev/null') return '';
  const s = path.replace(/\\/g, '/'); const k = s.indexOf('/'); return k >= 0 ? s.slice(k + 1) : s;
}
function cleanPathToken(p: string): string {
  const t = p.trim().replace(/^"+|"+$/g, '').replace(/^'+|'+$/g, '');
  return t.split(/[\t ]/)[0] ?? t;
}
function stripAB(path: string): string {
  const p = cleanPathToken(path);
  if (p === '/dev/null') return '/dev/null';
  const m = p.match(/^(?:a|b)\/(.+)$/);
  return m ? m[1]! : p;
}
function parseUnified(lines: string[]): UFile[] {
  const files: UFile[] = [];
  let i = 0;
  while (i < lines.length) {
    const l = lines[i]!;
    if (l.startsWith('diff --git ')) {
      const rest = l.slice(11).trim();
      const parts = rest.split(/\s+/);
      const aTok = parts[0] ?? rest;
      const bTok = parts.length > 1 ? parts[parts.length - 1]! : aTok;
      const f: UFile = { path: stripAB(bTok), delPath: stripAB(aTok), newPath: stripAB(bTok), created: false, deleted: false, oldLines: null, hunks: [], line: i + 1 };
      files.push(f); i++;
      while (i < lines.length) {
        const x = lines[i]!;
        if (x.startsWith('diff --git ')) break;
        if (x.startsWith('index ') || x.startsWith('similarity index ') || x.startsWith('dissimilarity index ') || x.startsWith('old mode ') || x.startsWith('new mode ') || x.startsWith('deleted file mode ') || x.startsWith('new file mode ') || x.startsWith('copy from ') || x.startsWith('copy to ')) {
          if (x.startsWith('new file mode ')) f.created = true;
          if (x.startsWith('deleted file mode ')) f.deleted = true;
          i++; continue;
        }
        if (x.startsWith('rename from ')) { f.delPath = cleanPathToken(x.slice(12)); i++; continue; }
        if (x.startsWith('rename to ')) { f.newPath = cleanPathToken(x.slice(10)); i++; continue; }
        if (x.startsWith('--- ')) {
          f.delPath = stripAB(x.slice(4));
          const p = lines[i + 1];
          if (p === undefined || !p.startsWith('+++ ')) throw new Exit2(`error: parse ${i + 2}`);
          f.newPath = stripAB(p.slice(4));
          f.path = f.newPath === '/dev/null' ? (f.delPath === '/dev/null' ? '' : f.delPath) : f.newPath;
          i += 2; continue;
        }
        if (x.startsWith('+++ ')) throw new Exit2(`error: parse ${i + 1}`);
        if (x.startsWith('@@')) break;
        i++; // ignore other header/prose lines
      }
      while (i < lines.length && lines[i]!.startsWith('@@')) {
        const m = lines[i]!.match(/^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/);
        if (!m) throw new Exit2(`error: parse ${i + 1}`);
        const oldStart = Number(m[1]); const oldCount = m[2] === undefined ? 1 : Number(m[2]);
        f.hunks.push({ oldStart, oldCount, lines: [] });
        i++;
        while (i < lines.length) {
          const x = lines[i]!;
          if (x.startsWith('@@')) break;
          if (x.startsWith('diff --git ')) break;
          if (x.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) break;
          if (x.startsWith('\\ No newline at end of file')) { f.hunks[f.hunks.length - 1]!.lines.push('\\'); i++; continue; }
          if (x === '') { f.hunks[f.hunks.length - 1]!.lines.push('\u0000'); i++; continue; }
          if (x[0] === ' ' || x[0] === '+' || x[0] === '-') { f.hunks[f.hunks.length - 1]!.lines.push(x); i++; continue; }
          break; // unknown line ends hunk body
        }
      }
      if (f.newPath === '/dev/null' || f.created === false && f.deleted === false && f.delPath !== '/dev/null' && f.newPath === '/dev/null') f.deleted = true;
      if (f.delPath === '/dev/null') f.created = true;
      if (f.path === '/dev/null') f.path = f.delPath !== '/dev/null' ? f.delPath : f.newPath;
      continue;
    }
    if (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      const delPath = stripAB(l.slice(4));
      const newPath = stripAB(lines[i + 1]!.slice(4));
      const path = newPath === '/dev/null' ? delPath : newPath;
      const f: UFile = { path, delPath, newPath, created: delPath === '/dev/null', deleted: newPath === '/dev/null', oldLines: null, hunks: [], line: i + 1 };
      files.push(f); i += 2;
      while (i < lines.length && lines[i]!.startsWith('@@')) {
        const m = lines[i]!.match(/^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/);
        if (!m) throw new Exit2(`error: parse ${i + 1}`);
        const oldStart = Number(m[1]); const oldCount = m[2] === undefined ? 1 : Number(m[2]);
        f.hunks.push({ oldStart, oldCount, lines: [] });
        i++;
        while (i < lines.length) {
          const x = lines[i]!;
          if (x.startsWith('@@')) break;
          if (x.startsWith('diff --git ')) break;
          if (x.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) break;
          if (x.startsWith('\\ No newline at end of file')) { f.hunks[f.hunks.length - 1]!.lines.push('\\'); i++; continue; }
          if (x === '') { f.hunks[f.hunks.length - 1]!.lines.push('\u0000'); i++; continue; }
          if (x[0] === ' ' || x[0] === '+' || x[0] === '-') { f.hunks[f.hunks.length - 1]!.lines.push(x); i++; continue; }
          break;
        }
      }
      continue;
    }
    if (l.startsWith('--- ')) { throw new Exit2(`error: parse ${i + 2}`); }
    i++; // ignore prose/fences/blank outside sections
  }
  if (files.length === 0) throw new Exit2('error: parse 1');
  for (const f of files) for (const h of f.hunks) {
    while (h.lines.length > 0 && h.lines[h.lines.length - 1] === '\u0000') h.lines.pop();
    for (let q = 0; q < h.lines.length; q++) if (h.lines[q] === '\u0000') h.lines[q] = ' ';
  }
  return files;
}
function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  const files = parseUnified(lines);
  return files.map((f) => (tree: Tree) => {
    const isCreate = f.created || f.delPath === '/dev/null';
    const isDelete = f.deleted || f.newPath === '/dev/null';
    const oldPath = (!isCreate && f.delPath && f.delPath !== '/dev/null') ? f.delPath : (f.path !== '/dev/null' ? f.path : '');
    const newPath = (!isDelete && f.newPath && f.newPath !== '/dev/null') ? f.newPath : (f.path !== '/dev/null' ? f.path : '');
    if (isCreate) { if (newPath === '') throw new Fail('unsafe', ''); ensureSafe(newPath); }
    else if (isDelete) { if (oldPath === '') throw new Fail('unsafe', ''); ensureSafe(oldPath); }
    else { if (oldPath === '' || newPath === '') throw new Fail('unsafe', ''); ensureSafe(oldPath); ensureSafe(newPath); }
    const st = isCreate ? null : tree.get(oldPath);
    if (isCreate) {
      if (tree.get(newPath) !== null) throw new Fail('exists', newPath);
      const out: string[] = [];
      for (const h of f.hunks) for (const x of h.lines) { if (x === '\\') continue; if (x[0] === '+' || x[0] === ' ') out.push(x.slice(1)); }
      const text = out.length > 0 ? out.join('\n') + '\n' : '';
      tree.set(newPath, { text, nl: '\n', final: out.length > 0 }); return;
    }
    if (isDelete) {
      if (st === null) throw new Fail('missing', oldPath);
      tree.set(oldPath, null); return;
    }
    if (st === null) throw new Fail('missing', oldPath);
    if (newPath !== oldPath && tree.get(newPath) !== null) throw new Fail('exists', newPath);
    const fileLines = splitFileLines(st.text, st.nl, st.final);
    let f2 = fileLines;
    let cursor = 0;
    let fileFinal = st.final;
    for (const h of f.hunks) {
      const bodyNoMarker = h.lines.filter((x)=>x!=='\\');
      const O = bodyNoMarker.filter((x) => (x[0] === ' ' || x[0] === '-')).map((x) => x.slice(1));
      const N = bodyNoMarker.filter((x) => (x[0] === ' ' || x[0] === '+')).map((x) => x.slice(1));
      const nIsCtx = bodyNoMarker.filter((x) => (x[0] === ' ' || x[0] === '+')).map((x) => x[0] === ' ');
      const fromPos = h.oldStart <= 0 ? 0 : h.oldStart - 1;
      if (h.oldCount === 0 && O.length === 0) {
        const pos = Math.max(cursor, Math.min(h.oldStart, f2.length));
        const outN = buildReplacement([], [], N, nIsCtx, 0);
        f2 = replaceAt(f2, pos, 0, outN); cursor = pos + outN.length; continue;
      }
      const found = chooseTier(f2, O, strict);
      if (!found) throw new Fail('no-match', f.path);
      let pos: number;
      const exact = found.occ.filter((x) => x === fromPos);
      if (exact.length > 0) pos = exact[0]!;
      else {
        const after = found.occ.filter((x) => x >= cursor);
        if (after.length === 1) pos = after[0]!;
        else if (after.length === 0 && found.occ.length === 1) pos = found.occ[0]!;
        else {
          const cands = after.length > 0 ? after : found.occ;
          let best = cands[0]!, bd = Math.abs(best - fromPos);
          for (let k = 1; k < cands.length; k++) { const d = Math.abs(cands[k]! - fromPos); if (d < bd) { best = cands[k]!; bd = d; } }
          pos = best;
        }
      }
      const outN = buildReplacement(f2.slice(pos, pos + O.length), O, N, nIsCtx, found.tier);
      f2 = replaceAt(f2, pos, O.length, outN);
      cursor = pos + outN.length;
      //  No newline at end of file marker
      const markers = h.lines.map((x,i)=>({x,i})).filter(z=>z.x==='\\');
      for(const mk of markers){
        const prev = h.lines[mk.i-1];
        if(prev===undefined) continue;
        const atEnd = (pos + outN.length === f2.length);
        if(atEnd && (prev[0]==='+' || prev[0]===' ')) fileFinal = false;
      }
      // if hunk touched EOF and last added/ctx line has no marker but original did? keep fileFinal as before; if marker indicates no final, set false
    }
    const text = joinFileLines(f2, st.nl, fileFinal);
    if (newPath !== oldPath) {
      tree.set(newPath, { text, nl: st.nl, final: st.final });
      tree.set(oldPath, null);
      tree.recordMove(oldPath, newPath);
    } else tree.set(oldPath, { text, nl: st.nl, final: st.final });
  });
}

// --- CLI (sections 1, 2, 3, 10) ---
function run(args: string[]): { code: number; out: string[] } {
  let format: Format | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') { ended = true; continue; }
    if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=')) {
        const v = a.slice(9);
        if (format !== null || !FORMATS.includes(v as Format)) return { code: 2, out: ['error: usage'] };
        format = v as Format;
      } else if (a === '--check') {
        if (check) return { code: 2, out: ['error: usage'] };
        check = true;
      } else if (a === '--strict') {
        if (strict) return { code: 2, out: ['error: usage'] };
        strict = true;
      } else return { code: 2, out: ['error: usage'] };
      continue;
    }
    pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try { text = readFileSync(file ?? 0, 'utf8'); } catch { if (file !== null) return { code: 2, out: ['error: no-patch'] }; }
  const lines = patchLines(text);
  const kind: Format | null = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    edits = kind === 'json' ? jsonEdits(text, lines)
      : kind === 'search-replace' ? srEdits(lines, strict)
      : kind === 'v4a' ? v4aEdits(lines, strict)
      : unifiedEdits(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = tree.snapshot();
    try { edit(tree); } catch (e) { if (!(e instanceof Fail)) throw e; tree.restore(before); fails.push(e); }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  // Build rename-aware output rows.
  const allPaths = new Set<string>([...tree.now.keys(), ...tree.orig.keys()]);
  const changed: {p:string; was:FileState; now:FileState}[] = [];
  for (const p of allPaths) {
    const was = tree.original(p);
    const now = tree.get(p);
    const wasText = was === null ? null : was.text;
    const nowText = now === null ? null : now.text;
    if (wasText === nowText) continue;
    changed.push({p, was, now});
  }
  const dels = changed.filter(c=>c.was!==null && c.now===null);
  const adds = changed.filter(c=>c.was===null && c.now!==null);
  const mods = changed.filter(c=>c.was!==null && c.now!==null);
  const usedDel = new Set<string>();
  const usedAdd = new Set<string>();
  const rows: {op:string; sortKey:string}[] = [];
  for (const [o,n] of tree.moves) {
    if (!usedDel.has(o) && !usedAdd.has(n)) { usedDel.add(o); usedAdd.add(n); rows.push({op:`R ${o} -> ${n}`, sortKey:n}); }
  }
  for (const d of dels) {
    if (usedDel.has(d.p)) continue;
    const match = adds.find(a=>!usedAdd.has(a.p) && a.now!.text === d.was!.text);
    if (match) { usedAdd.add(match.p); rows.push({op:`R ${d.p} -> ${match.p}`, sortKey:match.p}); }
    else rows.push({op:`D ${d.p}`, sortKey:d.p});
  }
  for (const a of adds) if (!usedAdd.has(a.p)) rows.push({op:`A ${a.p}`, sortKey:a.p});
  for (const m of mods) rows.push({op:`M ${m.p}`, sortKey:m.p});
  rows.sort((a,b)=>Buffer.compare(Buffer.from(a.sortKey), Buffer.from(b.sortKey)));
  const outRows = rows.map(r=>r.op);
  if (!check) {
    for (const c of changed) {
      const now = c.now;
      if (now === null) rmSync(c.p, { force: true });
      else { mkdirSync(dirname(c.p), { recursive: true }); writeFileSync(c.p, now.text); }
    }
  }
  return { code: 0, out: [...outRows, `ok: ${outRows.length} ${outRows.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
