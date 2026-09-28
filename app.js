/* Grid Broadcast
 *
 * Mobile agents on the grid Pm x Pn. Each round the tree player picks a
 * spanning tree, then the agent player moves agents along tree edges. Agents
 * that share a vertex share knowledge.
 *
 * Vertices are numbered v = r*n + c; row r is labelled a, b, c, ... and column c
 * is labelled 1..n, so vertex b3 is (r, c) = (1, 2).
 * Edges are numbered: vertical edges first (row by row), then horizontal edges.
 */
(() => {
  'use strict';

  const SVGNS = 'http://www.w3.org/2000/svg';
  const STORE_KEY = 'grid-broadcast/v1';
  const GAP = 104, PAD_L = 72, PAD_R = 50, PAD_T = 62, PAD_B = 42, VR = 24;
  const MAX_ROWS = 10, MAX_COLS = 30, MAX_AGENTS = 80, MAX_STEPS = 6, PLAY_MS = 1100;

  const $ = (sel) => document.querySelector(sel);
  const $$ = (sel) => Array.from(document.querySelectorAll(sel));

  // ---------------------------------------------------------------- graph

  let G;

  function buildGraph(rows, n) {
    const V = rows * n, edges = [], adj = Array.from({ length: V }, () => []);
    const add = (a, b) => {
      const id = edges.length;
      edges.push({ id, a, b });
      adj[a].push({ v: b, e: id });
      adj[b].push({ v: a, e: id });
    };
    for (let r = 0; r + 1 < rows; r++) for (let c = 0; c < n; c++) add(r * n + c, (r + 1) * n + c);
    for (let r = 0; r < rows; r++) for (let c = 0; c + 1 < n; c++) add(r * n + c, r * n + c + 1);
    return { rows, n, V, edges, adj };
  }

  const edgeCount = (rows, n) => rows * (n - 1) + (rows - 1) * n;
  const rowName = (r) => String.fromCharCode(97 + r);
  const vx = (v) => PAD_L + (v % G.n) * GAP;
  const vy = (v) => PAD_T + Math.floor(v / G.n) * GAP;
  const label = (v) => rowName(Math.floor(v / G.n)) + ((v % G.n) + 1);
  const labelHTML = (v) => `<span class="vl"><i>${rowName(Math.floor(v / G.n))}</i><sub>${(v % G.n) + 1}</sub></span>`;

  // Number of spanning trees of Pm x Pn by the matrix-tree theorem: the Laplacian
  // eigenvalues are (2 - 2cos(pi j/m)) + (2 - 2cos(pi k/n)). Returns HTML.
  function spanningTreeCount(rows, n) {
    const lam = (k, m) => 2 - 2 * Math.cos((Math.PI * k) / m);
    let log = -Math.log10(rows * n), prod = 1 / (rows * n);
    for (let j = 0; j < rows; j++) {
      for (let k = 0; k < n; k++) {
        if (!j && !k) continue;
        const x = lam(j, rows) + lam(k, n);
        log += Math.log10(x);
        prod *= x;
      }
    }
    if (log < 12) return Math.round(prod).toLocaleString('en-US');
    const exp = Math.floor(log);
    return `about ${(10 ** (log - exp)).toFixed(2)} × 10<sup>${exp}</sup>`;
  }

  function makeUF(N) {
    const p = Array.from({ length: N }, (_, i) => i);
    const find = (x) => { while (p[x] !== x) { p[x] = p[p[x]]; x = p[x]; } return x; };
    return { find, union(a, b) { a = find(a); b = find(b); if (a === b) return false; p[a] = b; return true; } };
  }

  // Components, edges lying on a cycle, and whether the selection is a spanning tree.
  function analyze(sel) {
    const uf = makeUF(G.V);
    let comps = G.V;
    for (const e of sel) if (uf.union(G.edges[e].a, G.edges[e].b)) comps--;
    const cycleEdges = new Set();
    for (const e of sel) {
      const u2 = makeUF(G.V);
      for (const f of sel) if (f !== e) u2.union(G.edges[f].a, G.edges[f].b);
      if (u2.find(G.edges[e].a) === u2.find(G.edges[e].b)) cycleEdges.add(e);
    }
    return { count: sel.size, comps, cycleEdges, valid: sel.size === G.V - 1 && comps === 1 };
  }

  const treeNeighbors = (v, tree) => G.adj[v].filter((x) => tree.has(x.e));

  // BFS in the tree from origin out to distance k: Map vertex -> { d, prev, e }.
  function treeBall(origin, k, tree) {
    const seen = new Map([[origin, { d: 0, prev: -1, e: -1 }]]);
    const queue = [origin];
    while (queue.length) {
      const u = queue.shift(), d = seen.get(u).d;
      if (d >= k) continue;
      for (const { v, e } of treeNeighbors(u, tree)) {
        if (!seen.has(v)) { seen.set(v, { d: d + 1, prev: u, e }); queue.push(v); }
      }
    }
    return seen;
  }

  function treePath(from, to, tree) {
    const ball = treeBall(from, Infinity, tree);
    if (!ball.has(to)) return [from];
    const path = [to];
    for (let u = to; u !== from;) { u = ball.get(u).prev; path.push(u); }
    return path.reverse();
  }

  function shuffle(arr) {
    for (let i = arr.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      [arr[i], arr[j]] = [arr[j], arr[i]];
    }
    return arr;
  }

  // Uniformly random spanning tree (Wilson's algorithm).
  function randomTree() {
    const inTree = new Array(G.V).fill(false), next = new Array(G.V), nextE = new Array(G.V);
    const root = Math.floor(Math.random() * G.V);
    inTree[root] = true;
    for (let i = 0; i < G.V; i++) {
      let u = i;
      while (!inTree[u]) {
        const nb = G.adj[u][Math.floor(Math.random() * G.adj[u].length)];
        next[u] = nb.v; nextE[u] = nb.e; u = nb.v;
      }
      for (u = i; !inTree[u]; u = next[u]) inTree[u] = true;
    }
    const out = [];
    for (let v = 0; v < G.V; v++) if (v !== root) out.push(nextE[v]);
    return out;
  }

  // Extend a forest to a spanning tree with randomly chosen extra edges.
  function fillTree(sel) {
    const uf = makeUF(G.V), out = new Set(sel);
    for (const e of sel) uf.union(G.edges[e].a, G.edges[e].b);
    for (const e of shuffle(G.edges.filter((x) => !out.has(x.id)))) if (uf.union(e.a, e.b)) out.add(e.id);
    return [...out];
  }

  // ---------------------------------------------------------------- state

  let S;
  const ui = {
    tool: 'addK',
    selected: null, // agent index selected in the move phase
    replay: null,   // history index being replayed, or null for the live game
    playing: null,  // interval id during replay playback
    undo: [],       // snapshots for undo within the current phase
    down: null,     // pointer gesture in progress
    stroke: null,   // edge-painting drag in the tree phase
    drag: null,
    dropV: null,
    view: null,
  };

  function sampleState() {
    const rows = 3, n = 6, at = (r, c) => r * n + c;
    return {
      version: 1,
      rows,
      n,
      rules: { steps: 1, exchange: 'end' },
      setup: [
        { pos: at(0, 0), know: true },
        { pos: at(1, 2), know: false },
        { pos: at(2, 1), know: false },
        { pos: at(0, 4), know: false },
        { pos: at(2, 5), know: false },
      ],
      phase: 'setup',
      history: [],
      tree: [],
      plan: { dest: [], log: [] },
    };
  }

  const clampInt = (x, lo, hi, dflt) => {
    const v = Math.round(Number(x));
    return Number.isFinite(v) ? Math.min(hi, Math.max(lo, v)) : dflt;
  };

  function validState(s) {
    try {
      if (!s || typeof s !== 'object') return null;
      const n = s.n, rows = s.rows ?? 2; // files saved before rows existed were ladders
      if (!Number.isInteger(n) || n < 2 || n > MAX_COLS) return null;
      if (!Number.isInteger(rows) || rows < 1 || rows > MAX_ROWS) return null;
      const V = rows * n, E = edgeCount(rows, n);
      const isV = (x) => Number.isInteger(x) && x >= 0 && x < V;
      const isE = (x) => Number.isInteger(x) && x >= 0 && x < E;
      if (!Array.isArray(s.setup) || s.setup.length > MAX_AGENTS || !s.setup.every((x) => x && isV(x.pos))) return null;

      let history = Array.isArray(s.history) ? s.history : [];
      const m = history[0]?.pos?.length ?? 0;
      for (const f of history) {
        if (!f || !['start', 'tree', 'move'].includes(f.kind)) return null;
        if (!Array.isArray(f.pos) || f.pos.length !== m || !f.pos.every(isV)) return null;
        if (!Array.isArray(f.know) || f.know.length !== m) return null;
        if (f.tree != null && (!Array.isArray(f.tree) || !f.tree.every(isE))) return null;
        if (f.kind !== 'start' && !Array.isArray(f.tree)) return null;
        f.know = f.know.map(Boolean);
        f.round = Number.isInteger(f.round) ? f.round : 0;
        if (f.kind === 'move') {
          f.moves = (Array.isArray(f.moves) ? f.moves : []).filter(
            (x) => x && Number.isInteger(x.a) && x.a >= 0 && x.a < m && Array.isArray(x.path) && x.path.every(isV));
        }
      }

      let phase = ['setup', 'tree', 'move', 'done'].includes(s.phase) ? s.phase : 'setup';
      if (!history.length || history[0].kind !== 'start') { phase = 'setup'; history = []; }
      const lastKind = history.length ? history[history.length - 1].kind : null;
      if (phase === 'move' && lastKind !== 'tree') phase = 'tree';
      if (phase === 'tree' && lastKind === 'tree') phase = 'move';
      if (phase === 'setup') history = [];

      return {
        version: 1,
        rows,
        n,
        rules: {
          steps: clampInt(s.rules?.steps, 1, MAX_STEPS, 1),
          exchange: s.rules?.exchange === 'land' ? 'land' : 'end',
        },
        setup: s.setup.map((x) => ({ pos: x.pos, know: !!x.know })),
        phase,
        history,
        tree: Array.isArray(s.tree) ? s.tree.filter(isE) : [],
        plan: {
          dest: Array.isArray(s.plan?.dest) ? s.plan.dest.map((x) => (isV(x) ? x : null)) : [],
          log: Array.isArray(s.plan?.log)
            ? s.plan.log.filter((x) => x && Number.isInteger(x.a) && x.a >= 0 && x.a < m && isV(x.to))
            : [],
        },
      };
    } catch {
      return null;
    }
  }

  function loadStored() {
    try {
      const raw = localStorage.getItem(STORE_KEY);
      return raw ? validState(JSON.parse(raw)) : null;
    } catch {
      return null;
    }
  }

  function save() {
    try { localStorage.setItem(STORE_KEY, JSON.stringify(S)); } catch { /* storage unavailable */ }
  }

  const last = () => S.history[S.history.length - 1];
  const roundsPlayed = () => S.history.filter((f) => f.kind === 'move').length;
  const countTrue = (arr) => arr.filter(Boolean).length;

  function lastTree() {
    for (let i = S.history.length - 1; i >= 0; i--) if (S.history[i].tree) return S.history[i].tree;
    return null;
  }

  // ---------------------------------------------------------------- rules

  // Every agent on a vertex with a knowledgeable agent becomes knowledgeable.
  function share(pos, know) {
    const lit = new Set();
    pos.forEach((v, a) => { if (know[a]) lit.add(v); });
    return pos.map((v, a) => !!know[a] || lit.has(v));
  }

  // Positions and knowledge implied by the moves planned so far this round.
  function liveMove() {
    const base = last(), tree = new Set(base.tree), k = S.rules.steps;
    if (S.rules.exchange === 'end') {
      const pos = [], paths = [];
      base.pos.forEach((o, a) => {
        const d = S.plan.dest[a];
        let p = d == null || d === o ? [o] : treePath(o, d, tree);
        if (p.length - 1 > k) p = [o];
        paths.push(p);
        pos.push(p[p.length - 1]);
      });
      return { base, tree, pos, paths, know: share(pos, base.know), used: paths.map((p) => p.length - 1) };
    }
    const pos = base.pos.slice(), know = base.know.slice(), paths = pos.map((v) => [v]);
    for (const { a, to } of S.plan.log) {
      pos[a] = to;
      paths[a].push(to);
      if (pos.some((v, b) => v === to && know[b])) pos.forEach((v, b) => { if (v === to) know[b] = true; });
    }
    return { base, tree, pos, paths, know, used: paths.map((p) => p.length - 1) };
  }

  // Where agent a may go next: Map vertex -> 'move' | 'return', plus tree edges to highlight.
  function targetsFor(a, mv) {
    const t = new Map(), hot = new Set(), origin = mv.base.pos[a], cur = mv.pos[a], k = S.rules.steps;
    if (S.rules.exchange === 'end') {
      for (const [v, info] of treeBall(origin, k, mv.tree)) {
        if (v !== cur) t.set(v, v === origin ? 'return' : 'move');
        if (info.e >= 0) hot.add(info.e);
      }
    } else {
      if (mv.used[a] < k) for (const { v, e } of treeNeighbors(cur, mv.tree)) { t.set(v, 'move'); hot.add(e); }
      if (cur !== origin && !t.has(origin)) t.set(origin, 'return');
    }
    return { t, hot };
  }

  // ---------------------------------------------------------------- actions

  function commit() { save(); render(); }

  function pushUndo() {
    ui.undo.push(JSON.stringify({ setup: S.setup, tree: S.tree, plan: S.plan }));
    if (ui.undo.length > 300) ui.undo.shift();
  }

  function undo() {
    if (ui.replay !== null || !ui.undo.length) return;
    const snap = JSON.parse(ui.undo.pop());
    if (S.phase === 'setup') { S.setup = snap.setup; syncCountInputs(); }
    else if (S.phase === 'tree') S.tree = snap.tree;
    else if (S.phase === 'move') S.plan = snap.plan;
    ui.selected = null;
    commit();
  }

  function startGame() {
    if (!S.setup.length) return;
    const pos = S.setup.map((x) => x.pos);
    const know = share(pos, S.setup.map((x) => x.know));
    S.history = [{ kind: 'start', round: 0, tree: null, pos, know }];
    S.tree = [];
    S.plan = { dest: [], log: [] };
    S.phase = know.every(Boolean) ? 'done' : 'tree';
    ui.undo = [];
    ui.selected = null;
    commit();
  }

  function setTree(edges) {
    pushUndo();
    S.tree = edges.slice();
    commit();
  }

  function confirmTree() {
    if (S.phase !== 'tree' || !analyze(new Set(S.tree)).valid) return;
    const b = last();
    S.history.push({
      kind: 'tree',
      round: roundsPlayed() + 1,
      tree: S.tree.slice().sort((x, y) => x - y),
      pos: b.pos.slice(),
      know: b.know.slice(),
    });
    S.phase = 'move';
    S.plan = { dest: [], log: [] };
    ui.undo = [];
    ui.selected = null;
    commit();
  }

  function redrawTree() {
    if (S.phase !== 'move') return;
    const f = S.history.pop();
    S.tree = f.tree.slice();
    S.plan = { dest: [], log: [] };
    S.phase = 'tree';
    ui.undo = [];
    ui.selected = null;
    commit();
  }

  function applyMove(a, v) {
    const mv = liveMove();
    const act = targetsFor(a, mv).t.get(v);
    if (!act) return false;
    pushUndo();
    if (S.rules.exchange === 'end') S.plan.dest[a] = v === mv.base.pos[a] ? null : v;
    else if (act === 'move') S.plan.log.push({ a, from: mv.pos[a], to: v });
    else S.plan.log = S.plan.log.filter((s) => s.a !== a);
    const after = liveMove();
    const moreSteps = S.rules.exchange === 'land' && after.used[a] < S.rules.steps;
    if (!moreSteps) ui.selected = null;
    commit();
    return true;
  }

  function resetMoves() {
    pushUndo();
    S.plan = { dest: [], log: [] };
    ui.selected = null;
    commit();
  }

  function endRound() {
    if (S.phase !== 'move') return;
    const mv = liveMove(), f = last();
    S.history.push({
      kind: 'move',
      round: f.round,
      tree: f.tree,
      pos: mv.pos,
      know: mv.know,
      moves: mv.paths.map((path, a) => ({ a, path })).filter((x) => x.path.length > 1),
      log: S.rules.exchange === 'land' ? S.plan.log.map((s) => ({ ...s })) : undefined,
    });
    S.tree = [];
    S.plan = { dest: [], log: [] };
    S.phase = mv.know.every(Boolean) ? 'done' : 'tree';
    ui.undo = [];
    ui.selected = null;
    commit();
  }

  function backToSetup() {
    stopPlay();
    ui.replay = null;
    ui.selected = null;
    ui.undo = [];
    S.phase = 'setup';
    S.history = [];
    S.tree = [];
    S.plan = { dest: [], log: [] };
    commit();
  }

  function placeRandom(m, k) {
    pushUndo();
    const spots = m <= G.V
      ? shuffle([...Array(G.V).keys()]).slice(0, m)
      : Array.from({ length: m }, () => Math.floor(Math.random() * G.V));
    // Number agents left to right so labels are easy to find.
    spots.sort((p, q) => (p % G.n) - (q % G.n) || p - q);
    const knowing = new Set(shuffle([...Array(m).keys()]).slice(0, k));
    S.setup = spots.map((pos, a) => ({ pos, know: knowing.has(a) }));
    syncCountInputs();
    commit();
  }

  // Change the grid size, pulling agents that fall off the edge onto the last row/column.
  function setSize(rows, n) {
    if (S.phase !== 'setup' || (rows === S.rows && n === S.n)) return;
    const old = S.n;
    for (const x of S.setup) {
      const r = Math.min(Math.floor(x.pos / old), rows - 1), c = Math.min(x.pos % old, n - 1);
      x.pos = r * n + c;
    }
    S.rows = rows;
    S.n = n;
    ui.undo = [];
    buildBoard();
    commit();
  }

  // ---------------------------------------------------------------- replay

  function enterReplay(i) {
    if (!S.history.length) return;
    stopPlay();
    ui.selected = null;
    ui.replay = Math.max(0, Math.min(S.history.length - 1, i));
    render();
  }

  function setReplay(i) {
    stopPlay();
    ui.replay = Math.max(0, Math.min(S.history.length - 1, i));
    render();
  }

  function exitReplay() {
    stopPlay();
    ui.replay = null;
    render();
  }

  function stopPlay() {
    if (ui.playing) { clearInterval(ui.playing); ui.playing = null; }
  }

  function togglePlay() {
    if (ui.playing) { stopPlay(); render(); return; }
    if (ui.replay >= S.history.length - 1) ui.replay = 0;
    ui.playing = setInterval(() => {
      if (ui.replay >= S.history.length - 1) stopPlay();
      else ui.replay++;
      render();
    }, PLAY_MS);
    render();
  }

  // Throw away everything after the replayed step and continue the game from there.
  function resumeFromReplay() {
    const i = ui.replay;
    if (i === null) return;
    if (i === S.history.length - 1) { exitReplay(); return; }
    const f = S.history[i];
    S.history = S.history.slice(0, i + 1);
    S.plan = { dest: [], log: [] };
    if (f.kind === 'tree') { S.phase = 'move'; S.tree = f.tree.slice(); }
    else { S.tree = []; S.phase = f.know.every(Boolean) ? 'done' : 'tree'; }
    stopPlay();
    ui.replay = null;
    ui.undo = [];
    commit();
  }

  // ---------------------------------------------------------------- import / export

  function exportJSON() {
    const L = label;
    return JSON.stringify({
      app: 'grid-broadcast',
      version: 1,
      saved: new Date().toISOString(),
      summary: {
        graph: `P${S.rows} x P${S.n}`,
        vertices: 'row letter + column number, e.g. b3 = second row, third column',
        rules: S.rules,
        start: S.history[0]
          ? S.history[0].pos.map((v, a) => ({ agent: a + 1, at: L(v), knowledgeable: S.history[0].know[a] }))
          : S.setup.map((x, a) => ({ agent: a + 1, at: L(x.pos), knowledgeable: x.know })),
        rounds: S.history.filter((f) => f.kind === 'move').map((f) => ({
          round: f.round,
          tree: f.tree.map((e) => `${L(G.edges[e].a)}-${L(G.edges[e].b)}`),
          moves: f.moves.map((x) => ({ agent: x.a + 1, path: x.path.map(L) })),
          knowledgeable: f.know.flatMap((k, a) => (k ? [a + 1] : [])),
        })),
      },
      state: S,
    }, null, 1);
  }

  function importJSON(text) {
    let obj;
    try { obj = JSON.parse(text); } catch {
      return 'That text is not valid JSON. Paste the whole file, including the outer braces.';
    }
    const s = validState(obj && obj.state ? obj.state : obj);
    if (!s) return 'This JSON does not describe a Grid Broadcast game.';
    stopPlay();
    S = s;
    ui.replay = null;
    ui.selected = null;
    ui.undo = [];
    buildBoard();
    syncCountInputs();
    commit();
    return null;
  }

  // ---------------------------------------------------------------- board

  const els = {
    board: $('#board'),
    gAxes: $('#g-axes'),
    gEdges: $('#g-edges'),
    gTrails: $('#g-trails'),
    gVertices: $('#g-vertices'),
    gAgents: $('#g-agents'),
    turn: $('#turn'),
    knowledge: $('#knowledge'),
    status: $('#status'),
    toast: $('#toast'),
    history: $('#history'),
    historyEmpty: $('#history-empty'),
    setupFields: $('#setup-fields'),
    lockbar: $('#lockbar'),
    inRows: $('#in-rows'),
    inN: $('#in-n'),
    inM: $('#in-m'),
    inK: $('#in-k'),
    inSteps: $('#in-steps'),
    exEnd: $('#ex-end'),
    exLand: $('#ex-land'),
    graphInfo: $('#graph-info'),
    rpSlider: $('#rp-slider'),
    rpLabel: $('#rp-label'),
    dlg: $('#dlg'),
    dlgForm: $('#dlg-form'),
    dlgTitle: $('#dlg-title'),
    dlgHint: $('#dlg-hint'),
    dlgFile: $('#dlg-file'),
    dlgText: $('#dlg-text'),
    dlgError: $('#dlg-error'),
    dlgOk: $('#dlg-ok'),
  };

  const btn = {
    start: $('#btn-start'),
    treeUndo: $('#btn-tree-undo'),
    treeClear: $('#btn-tree-clear'),
    treeAll: $('#btn-tree-all'),
    treeRandom: $('#btn-tree-random'),
    treeFill: $('#btn-tree-fill'),
    treeLast: $('#btn-tree-last'),
    treeConfirm: $('#btn-tree-confirm'),
    moveUndo: $('#btn-move-undo'),
    moveReset: $('#btn-move-reset'),
    moveRetree: $('#btn-move-retree'),
    moveEnd: $('#btn-move-end'),
    doneReplay: $('#btn-done-replay'),
    doneSetup: $('#btn-done-setup'),
    rpFirst: $('#rp-first'),
    rpPrev: $('#rp-prev'),
    rpPlay: $('#rp-play'),
    rpNext: $('#rp-next'),
    rpLast: $('#rp-last'),
    rpResume: $('#rp-resume'),
    rpExit: $('#rp-exit'),
    randomPlace: $('#btn-random-place'),
    clearAgents: $('#btn-clear-agents'),
    backSetup: $('#btn-back-setup'),
    replay: $('#btn-replay'),
    copy: $('#btn-copy'),
    download: $('#btn-download'),
    load: $('#btn-load'),
  };

  let edgeEls = [], vertexEls = [], agentEls = [];

  function svg(tag, attrs = {}) {
    const el = document.createElementNS(SVGNS, tag);
    for (const k in attrs) el.setAttribute(k, attrs[k]);
    return el;
  }

  function buildBoard() {
    G = buildGraph(S.rows, S.n);
    const W = PAD_L + PAD_R + (G.n - 1) * GAP, H = PAD_T + PAD_B + (G.rows - 1) * GAP;
    const b = els.board;
    b.setAttribute('viewBox', `0 0 ${W} ${H}`);
    // Scale up to 1.45x, but keep tall grids from growing past ~640px high.
    const maxW = W * Math.min(1.45, 640 / H);
    b.style.maxWidth = Math.round(maxW) + 'px';
    b.style.minWidth = Math.round(Math.min(W * 0.6, maxW)) + 'px';
    for (const g of [els.gAxes, els.gEdges, els.gTrails, els.gVertices, els.gAgents]) g.replaceChildren();

    for (let c = 0; c < G.n; c++) {
      const t = svg('text', { x: PAD_L + c * GAP, y: PAD_T - VR - 14, class: 'axis-col' });
      t.textContent = c + 1;
      els.gAxes.append(t);
    }
    for (let r = 0; r < G.rows; r++) {
      const t = svg('text', { x: PAD_L - VR - 22, y: PAD_T + r * GAP + 6, class: 'axis-row' });
      t.textContent = rowName(r);
      els.gAxes.append(t);
    }

    edgeEls = G.edges.map((e) => {
      const g = svg('g', { class: 'edge', 'data-e': e.id });
      const c = { x1: vx(e.a), y1: vy(e.a), x2: vx(e.b), y2: vy(e.b) };
      g.append(svg('line', { ...c, class: 'edge-line' }), svg('line', { ...c, class: 'edge-hit' }));
      els.gEdges.append(g);
      return g;
    });

    vertexEls = [];
    for (let v = 0; v < G.V; v++) {
      const cx = vx(v), cy = vy(v);
      const g = svg('g', { class: 'vertex', 'data-v': v });
      g.append(svg('circle', { cx, cy, r: VR + 9, class: 'vertex-hit' }), svg('circle', { cx, cy, r: VR, class: 'vertex-disc' }));
      const name = svg('title');
      name.textContent = label(v);
      g.append(name);
      els.gVertices.append(g);
      vertexEls.push(g);
    }
    agentEls = [];
  }

  function syncAgentEls(m) {
    while (agentEls.length < m) {
      const a = agentEls.length;
      const g = svg('g', { class: 'agent', 'data-a': a });
      g.append(svg('circle', { r: 12.5, class: 'agent-halo' }), svg('circle', { r: 9.5, class: 'agent-body' }));
      const t = svg('text', { y: 3.9, class: 'agent-num' });
      t.textContent = a + 1;
      g.append(t);
      g._fresh = true;
      els.gAgents.append(g);
      agentEls.push(g);
    }
    while (agentEls.length > m) agentEls.pop().remove();
  }

  // Offsets for k agents sharing a vertex, and the token scale.
  function cluster(k) {
    if (k === 1) return { offs: [[0, 0]], s: 1.15 };
    if (k === 2) return { offs: [[-10.5, 0], [10.5, 0]], s: 0.95 };
    if (k === 3) return { offs: [[-10, -6], [10, -6], [0, 10.5]], s: 0.9 };
    if (k === 4) return { offs: [[-9.5, -9.5], [9.5, -9.5], [-9.5, 9.5], [9.5, 9.5]], s: 0.85 };
    const R = 14.5, s = Math.max(0.36, Math.min(0.72, (R * Math.sin(Math.PI / k) - 0.6) / 9.5));
    const offs = Array.from({ length: k }, (_, i) => {
      const t = -Math.PI / 2 + (2 * Math.PI * i) / k;
      return [R * Math.cos(t), R * Math.sin(t)];
    });
    return { offs, s };
  }

  function agentsAt(v, pos) {
    const out = [];
    pos.forEach((p, a) => { if (p === v) out.push(a); });
    return out;
  }

  function placeAgents(view) {
    syncAgentEls(view.pos.length);
    const groups = new Map();
    view.pos.forEach((v, a) => {
      if (!groups.has(v)) groups.set(v, []);
      groups.get(v).push(a);
    });
    for (const [v, list] of groups) {
      const { offs, s } = cluster(list.length);
      list.forEach((a, i) => {
        const el = agentEls[a];
        const dragging = ui.drag && ui.drag.a === a;
        let c = 'agent';
        if (view.know[a]) c += ' know';
        if (view.learning[a]) c += ' learning';
        if (ui.selected === a) c += ' selected';
        if (s < 0.58) c += ' tiny';
        if (dragging) c += ' dragging';
        el.setAttribute('class', c);
        if (dragging) return;
        const tf = `translate(${vx(v) + offs[i][0]}px, ${vy(v) + offs[i][1]}px) scale(${s})`;
        if (el._fresh) {
          el.style.transition = 'none';
          el.style.transform = tf;
          el.getBoundingClientRect();
          el.style.transition = '';
          el._fresh = false;
        } else {
          el.style.transform = tf;
        }
      });
    }
  }

  function drawTrails(paths) {
    const g = els.gTrails;
    g.replaceChildren();
    for (const { path } of paths) {
      for (let i = 0; i + 1 < path.length; i++) {
        const p = path[i], q = path[i + 1];
        const x1 = vx(p), y1 = vy(p), x2 = vx(q), y2 = vy(q);
        const L = Math.hypot(x2 - x1, y2 - y1), ux = (x2 - x1) / L, uy = (y2 - y1) / L;
        // Offset to the right of the direction of travel so opposite moves don't overlap.
        const nx = -uy * 8, ny = ux * 8;
        g.append(svg('line', {
          x1: x1 + ux * (VR + 5) + nx, y1: y1 + uy * (VR + 5) + ny,
          x2: x2 - ux * (VR + 9) + nx, y2: y2 - uy * (VR + 9) + ny,
          class: 'trail', 'marker-end': 'url(#arrowhead)',
        }));
      }
    }
  }

  // ---------------------------------------------------------------- view

  function computeView() {
    const none = { targets: new Map(), hot: new Set(), paths: [] };
    const learnedSince = (f, prev) => f.know.map((k, a) => f.kind === 'move' && k && !!prev && !prev.know[a]);

    if (ui.replay !== null) {
      const f = S.history[ui.replay], prev = S.history[ui.replay - 1];
      return {
        ...none, mode: 'replay', frame: f, pos: f.pos, know: f.know,
        learning: learnedSince(f, prev),
        tree: f.tree ? new Set(f.tree) : null,
        paths: f.kind === 'move' ? f.moves : [],
      };
    }
    if (S.phase === 'setup') {
      const pos = S.setup.map((x) => x.pos);
      return { ...none, mode: 'setup', pos, know: S.setup.map((x) => x.know), learning: pos.map(() => false), tree: null };
    }
    if (S.phase === 'tree') {
      const b = last(), sel = new Set(S.tree);
      return { ...none, mode: 'tree', pos: b.pos, know: b.know, learning: b.pos.map(() => false), tree: sel, analysis: analyze(sel) };
    }
    if (S.phase === 'move') {
      const mv = liveMove();
      const tg = ui.selected !== null ? targetsFor(ui.selected, mv) : { t: new Map(), hot: new Set() };
      return {
        mode: 'move', mv, pos: mv.pos, know: mv.know,
        learning: mv.know.map((k, a) => k && !mv.base.know[a]),
        tree: mv.tree, targets: tg.t, hot: tg.hot,
        paths: mv.paths.map((path, a) => ({ a, path })).filter((x) => x.path.length > 1),
      };
    }
    const f = last(), prev = S.history[S.history.length - 2];
    return {
      ...none, mode: 'done', frame: f, pos: f.pos, know: f.know,
      learning: learnedSince(f, prev),
      tree: f.tree ? new Set(f.tree) : null,
      paths: f.kind === 'move' ? f.moves : [],
    };
  }

  function render() {
    const view = computeView();
    ui.view = view;
    els.board.setAttribute('class', `board mode-${view.mode}`);

    for (const e of G.edges) {
      let c = 'edge';
      if (view.mode === 'tree') {
        if (view.tree.has(e.id)) c += view.analysis.cycleEdges.has(e.id) ? ' sel cyc' : ' sel';
      } else if (view.tree) {
        c += view.tree.has(e.id) ? ' tree' : ' off';
      }
      if (view.hot.has(e.id)) c += ' hot';
      edgeEls[e.id].setAttribute('class', c);
    }

    for (let v = 0; v < G.V; v++) {
      const t = view.targets.get(v);
      let c = 'vertex';
      if (t) c += ' target';
      if (t === 'return') c += ' return';
      if (ui.dropV === v) c += ' drop';
      vertexEls[v].setAttribute('class', c);
    }

    drawTrails(view.paths);
    placeAgents(view);
    renderTurn(view);
    renderKnowledge(view);
    renderStatus(view);
    renderActions(view);
    renderPanels();
    renderHistory();
  }

  function turnSteps(i) {
    const cls = (j) => (j === i ? 'on' : j < i ? 'past' : '');
    return `<ol class="turn-steps"><li class="${cls(0)}">Tree player</li><li class="${cls(1)}">Agent player</li></ol>`;
  }

  function renderTurn(view) {
    let html;
    if (view.mode === 'setup') {
      html = '<span class="turn-title">Setup</span><span class="turn-note">Place agents, then start the game</span>';
    } else if (view.mode === 'replay') {
      const f = view.frame;
      html = `<span class="chip">Replay</span><span class="turn-title">${f.kind === 'start' ? 'Start' : `Round ${f.round}`}</span>`;
      if (f.kind !== 'start') html += turnSteps(f.kind === 'tree' ? 0 : 1);
    } else if (view.mode === 'done') {
      const r = roundsPlayed();
      html = `<span class="chip good">Complete</span><span class="turn-title">Everyone knows</span><span class="turn-note">${r} round${r === 1 ? '' : 's'}</span>`;
    } else {
      html = `<span class="turn-title">Round ${roundsPlayed() + 1}</span>${turnSteps(view.mode === 'tree' ? 0 : 1)}`;
    }
    els.turn.innerHTML = html;
  }

  function renderKnowledge(view) {
    const m = view.pos.length, k = countTrue(view.know);
    const dots = view.know.map((kn, a) =>
      `<i class="kd${kn ? ' know' : ''}${view.learning[a] ? ' learning' : ''}" title="Agent ${a + 1}: ${kn ? 'knowledgeable' : 'ignorant'}"></i>`).join('');
    els.knowledge.innerHTML = m
      ? `<span class="k-count"><b>${k}</b> of ${m} knowledgeable</span><span class="k-dots" aria-hidden="true">${dots}</span>`
      : '<span class="k-count">No agents yet</span>';
  }

  function agentsList(ids) {
    if (ids.length === 1) return `Agent ${ids[0]}`;
    return `Agents ${ids.slice(0, -1).join(', ')} and ${ids[ids.length - 1]}`;
  }

  function renderStatus(view) {
    const m = view.pos.length;
    let html = '';
    switch (view.mode) {
      case 'setup': {
        const tips = {
          addK: 'Click a vertex to add a <b>knowledgeable</b> agent.',
          addI: 'Click a vertex to add an <b>ignorant</b> agent.',
          toggle: 'Click an agent to switch it between knowledgeable and ignorant.',
          remove: 'Click an agent to remove it.',
        };
        html = `${tips[ui.tool]} Drag agents to move them.`;
        if (!m) html += ' <span class="warn">Add at least one agent to start.</span>';
        else if (!view.know.some(Boolean)) html += ' <span class="warn">No agent is knowledgeable yet, so nothing can spread.</span>';
        break;
      }
      case 'tree': {
        const an = view.analysis, need = G.V - 1;
        html = `<span class="num"><b>${an.count}</b>/${need}</span> edges. `;
        if (an.valid) html += 'This is a spanning tree. Confirm it to pass the turn to the agent player.';
        else if (!an.count) html += 'Click edges or drag across them to add them to the tree, or choose a random tree. Dragging across chosen edges removes them.';
        else {
          if (an.cycleEdges.size) html += '<span class="warn">Red edges lie on a cycle; remove one edge from each cycle.</span> ';
          if (an.comps > 1) {
            html += `The edges form ${an.comps} separate pieces`;
            html += an.cycleEdges.size ? '.' : `; add ${need - an.count} more to connect them.`;
          }
        }
        break;
      }
      case 'move': {
        const mv = view.mv, moved = mv.used.filter((u) => u > 0).length;
        if (ui.selected !== null) {
          const a = ui.selected, left = S.rules.steps - mv.used[a];
          html = `Agent <b>${a + 1}</b> at ${labelHTML(mv.pos[a])}: click a highlighted vertex to move it`;
          if (S.rules.exchange === 'land' && S.rules.steps > 1) html += ` (${left} step${left === 1 ? '' : 's'} left)`;
          html += '. <span class="quiet">Esc cancels.</span>';
        } else {
          html = 'Click an agent, then a highlighted vertex, to move it along the tree. Agents may also stay put.';
        }
        html += ` <span class="quiet">${moved} of ${m} moved.</span>`;
        const learners = view.learning.flatMap((l, a) => (l ? [a + 1] : []));
        if (learners.length) html += ` ${agentsList(learners)} ${S.rules.exchange === 'end' ? 'will learn' : 'learned'} this round.`;
        break;
      }
      case 'replay': {
        const f = view.frame;
        if (f.kind === 'start') html = 'Starting positions.';
        else if (f.kind === 'tree') html = `Round ${f.round}: the tree player chose this spanning tree.`;
        else {
          const learned = view.learning.flatMap((l, a) => (l ? [a + 1] : []));
          const n = f.moves.length;
          html = `Round ${f.round}: ${n ? `${n} agent${n === 1 ? '' : 's'} moved` : 'no agent moved'}. `;
          html += learned.length ? `${agentsList(learned)} learned.` : 'Nobody new learned anything.';
        }
        break;
      }
      case 'done': {
        const r = roundsPlayed();
        html = `All ${m} agents are knowledgeable ${r === 0 ? 'from the start' : `after ${r} round${r === 1 ? '' : 's'}`}. Replay the game or go back to setup to try again.`;
        break;
      }
    }
    els.status.innerHTML = html;
  }

  const ICON_PLAY = '<svg viewBox="0 0 16 16" aria-hidden="true"><path d="M5 3.5v9l7.5-4.5z"/></svg>';
  const ICON_PAUSE = '<svg viewBox="0 0 16 16" aria-hidden="true"><path d="M4.5 3.5h2.5v9H4.5zM9 3.5h2.5v9H9z"/></svg>';

  function renderActions(view) {
    for (const g of $$('.actions[data-for]')) g.hidden = g.dataset.for !== view.mode;
    if (view.mode === 'setup') {
      for (const b of $$('[data-tool]')) b.setAttribute('aria-pressed', String(b.dataset.tool === ui.tool));
      btn.start.disabled = !S.setup.length;
    } else if (view.mode === 'tree') {
      const an = view.analysis;
      btn.treeUndo.disabled = !ui.undo.length;
      btn.treeClear.disabled = !an.count;
      btn.treeAll.disabled = an.count === G.edges.length;
      btn.treeFill.disabled = an.valid || an.cycleEdges.size > 0;
      btn.treeLast.disabled = !lastTree();
      btn.treeConfirm.disabled = !an.valid;
    } else if (view.mode === 'move') {
      btn.moveUndo.disabled = !ui.undo.length;
      btn.moveReset.disabled = !view.mv.used.some((u) => u > 0);
    } else if (view.mode === 'replay') {
      const N = S.history.length, i = ui.replay;
      els.rpSlider.max = String(N - 1);
      els.rpSlider.value = String(i);
      els.rpLabel.textContent = `Step ${i + 1} of ${N}`;
      btn.rpFirst.disabled = btn.rpPrev.disabled = i === 0;
      btn.rpNext.disabled = btn.rpLast.disabled = i === N - 1;
      btn.rpPlay.innerHTML = ui.playing ? ICON_PAUSE : ICON_PLAY;
      btn.rpPlay.setAttribute('aria-label', ui.playing ? 'Pause' : 'Play');
      btn.rpResume.hidden = i === N - 1;
    }
  }

  function setVal(input, v) {
    if (document.activeElement !== input) input.value = v;
  }

  function syncCountInputs() {
    els.inM.value = S.setup.length || 1;
    els.inK.value = S.setup.filter((x) => x.know).length;
  }

  function renderPanels() {
    const inSetup = S.phase === 'setup';
    els.setupFields.disabled = !inSetup;
    els.lockbar.hidden = inSetup;
    setVal(els.inRows, S.rows);
    setVal(els.inN, S.n);
    setVal(els.inSteps, S.rules.steps);
    els.exEnd.checked = S.rules.exchange === 'end';
    els.exLand.checked = S.rules.exchange === 'land';
    if (els.graphInfo.dataset.size !== `${G.rows}x${G.n}`) {
      const er = Math.min(1, G.rows - 1), ec = Math.min(2, G.n - 1);
      els.graphInfo.dataset.size = `${G.rows}x${G.n}`;
      els.graphInfo.innerHTML =
        `<b>${G.V}</b> vertices, <b>${G.edges.length}</b> edges. ` +
        `Every spanning tree has <b>${G.V - 1}</b> edges, and there are <b>${spanningTreeCount(G.rows, G.n)}</b> of them. ` +
        `Vertex ${labelHTML(er * G.n + ec)} is in row ${rowName(er)}, column ${ec + 1}.`;
    }
    btn.replay.disabled = S.history.length < 2;
  }

  function moveSummary(f) {
    if (!f.moves.length) return '<span class="h-live">no moves</span>';
    return f.moves.map(({ a, path }) =>
      `<span class="h-mv"><b class="tok${f.know[a] ? ' know' : ''}">${a + 1}</b>${path.map(labelHTML).join('→')}</span>`).join('');
  }

  function renderHistory() {
    const H = S.history, list = els.history;
    els.historyEmpty.hidden = H.length > 0;
    if (!H.length) { list.replaceChildren(); return; }
    const m = H[0].pos.length, cur = ui.replay;
    const chip = (i, text) => `<button type="button" class="h-chip${cur === i ? ' on' : ''}" data-i="${i}">${text}</button>`;
    const rows = [
      `<li class="h-row"><span class="h-r">Start</span><span class="h-body">${chip(0, 'Starting positions')}</span><span class="h-k">${countTrue(H[0].know)}/${m}</span></li>`,
    ];
    for (let i = 1; i < H.length; i += 2) {
      const t = H[i], mv = H[i + 1];
      let body = chip(i, 'Tree'), k = '';
      if (mv) {
        body += chip(i + 1, 'Moves') + `<span class="h-moves">${moveSummary(mv)}</span>`;
        const now = countTrue(mv.know), before = countTrue(H[i - 1].know);
        k = `${now}/${m}${now > before ? ` <em>+${now - before}</em>` : ''}`;
      } else {
        body += '<span class="h-live">agents moving…</span>';
      }
      rows.push(`<li class="h-row"><span class="h-r">R${t.round}</span><span class="h-body">${body}</span><span class="h-k">${k}</span></li>`);
    }
    if (S.phase === 'tree') {
      rows.push(`<li class="h-row"><span class="h-r">R${roundsPlayed() + 1}</span><span class="h-body"><span class="h-live">choosing a tree…</span></span><span class="h-k"></span></li>`);
    }
    list.innerHTML = rows.join('');

    const on = list.querySelector('.h-chip.on');
    if (on) {
      const li = on.closest('li'), top = li.offsetTop, bottom = top + li.offsetHeight;
      if (top < list.scrollTop || bottom > list.scrollTop + list.clientHeight) list.scrollTop = top - list.clientHeight / 2;
    } else if (cur === null) {
      list.scrollTop = list.scrollHeight;
    }
  }

  let toastTimer;
  function toast(msg) {
    els.toast.textContent = msg;
    els.toast.classList.add('show');
    clearTimeout(toastTimer);
    toastTimer = setTimeout(() => els.toast.classList.remove('show'), 2200);
  }

  // Two-click confirmation for actions that throw work away.
  function armed(b, prompt, fn) {
    if (b.dataset.armed) {
      clearTimeout(b._armTimer);
      delete b.dataset.armed;
      b.textContent = b.dataset.label;
      fn();
      return;
    }
    b.dataset.label = b.textContent;
    b.dataset.armed = '1';
    b.textContent = prompt;
    b._armTimer = setTimeout(() => { delete b.dataset.armed; b.textContent = b.dataset.label; }, 3500);
  }

  function confirmDiscard(b) {
    if (S.history.length <= 1) backToSetup();
    else armed(b, 'Discard this game?', backToSetup);
  }

  // ---------------------------------------------------------------- pointer input

  function toSvgPoint(e) {
    const ctm = els.board.getScreenCTM();
    return ctm ? new DOMPoint(e.clientX, e.clientY).matrixTransform(ctm.inverse()) : { x: 0, y: 0 };
  }

  function nearestVertex(p, max = 48) {
    let best = null, bd = max;
    for (let v = 0; v < G.V; v++) {
      const d = Math.hypot(p.x - vx(v), p.y - vy(v));
      if (d < bd) { bd = d; best = v; }
    }
    return best;
  }

  const canDrag = () => ui.replay === null && (S.phase === 'setup' || S.phase === 'move');

  function setDrop(v) {
    if (ui.dropV === v) return;
    if (ui.dropV !== null) vertexEls[ui.dropV].classList.remove('drop');
    ui.dropV = v;
    if (v !== null) vertexEls[v].classList.add('drop');
  }

  function dropAllowed(a, v) {
    if (v === null) return false;
    if (S.phase === 'setup') return true;
    return ui.view.targets.has(v);
  }

  // ---- tree phase: click or drag across edges to paint them in or out

  // Distance from point p to the segment of edge e.
  function segDist(p, e) {
    const x1 = vx(e.a), y1 = vy(e.a), dx = vx(e.b) - x1, dy = vy(e.b) - y1;
    const t = Math.max(0, Math.min(1, ((p.x - x1) * dx + (p.y - y1) * dy) / (dx * dx + dy * dy)));
    return Math.hypot(p.x - x1 - t * dx, p.y - y1 - t * dy);
  }

  // The edge under point p, ignoring the vertex discs where several edges meet.
  function edgeAt(p, tol = 16) {
    if (nearestVertex(p, VR + 2) !== null) return null;
    let best = null, bd = tol;
    for (const e of G.edges) {
      const d = segDist(p, e);
      if (d < bd) { bd = d; best = e.id; }
    }
    return best;
  }

  // The first edge a stroke touches decides whether the stroke adds or removes.
  function paintEdge(e) {
    if (S.phase !== 'tree' || ui.replay !== null) return;
    const s = ui.stroke, sel = new Set(S.tree), has = sel.has(e);
    if (s.mode === null) s.mode = has ? 'remove' : 'add';
    if ((s.mode === 'add') === has) return;
    if (!s.changed) { pushUndo(); s.changed = true; }
    if (has) sel.delete(e); else sel.add(e);
    S.tree = [...sel];
    render();
  }

  function beginStroke(e) {
    ui.stroke = { id: e.pointerId, mode: null, changed: false, last: toSvgPoint(e) };
    try { els.board.setPointerCapture(e.pointerId); } catch { /* ignore */ }
    const el = e.target.closest('[data-e]');
    if (el) paintEdge(Number(el.dataset.e));
  }

  function strokeMove(e) {
    const s = ui.stroke;
    if (e.pointerId !== s.id) return;
    const p = toSvgPoint(e), a = s.last;
    // Sample along the pointer's path so a fast sweep doesn't skip edges.
    const steps = Math.max(1, Math.ceil(Math.hypot(p.x - a.x, p.y - a.y) / 6));
    for (let i = 1; i <= steps; i++) {
      const hit = edgeAt({ x: a.x + ((p.x - a.x) * i) / steps, y: a.y + ((p.y - a.y) * i) / steps });
      if (hit !== null) paintEdge(hit);
    }
    s.last = p;
  }

  function endStroke() {
    const s = ui.stroke;
    ui.stroke = null;
    if (s && s.changed) save();
  }

  els.board.addEventListener('pointerdown', (e) => {
    if (e.button !== 0) return;
    if (ui.replay === null && S.phase === 'tree') { beginStroke(e); return; }
    const el = e.target.closest('[data-a],[data-v],[data-e]');
    const a = el && el.dataset.a !== undefined ? Number(el.dataset.a) : null;
    ui.down = { el, a, x: e.clientX, y: e.clientY, id: e.pointerId, moved: false };
    if (a !== null && canDrag()) {
      try { els.board.setPointerCapture(e.pointerId); } catch { /* ignore */ }
    }
  });

  els.board.addEventListener('pointermove', (e) => {
    if (ui.stroke) { strokeMove(e); return; }
    const d = ui.down;
    if (!d || d.a === null || e.pointerId !== d.id || !canDrag()) return;
    if (!d.moved) {
      if (Math.hypot(e.clientX - d.x, e.clientY - d.y) < 5) return;
      d.moved = true;
      ui.drag = d;
      if (S.phase === 'move') ui.selected = d.a;
      render();
      els.gAgents.append(agentEls[d.a]);
    }
    const p = toSvgPoint(e);
    agentEls[d.a].style.transform = `translate(${p.x}px, ${p.y}px) scale(1.2)`;
    const v = nearestVertex(p);
    setDrop(dropAllowed(d.a, v) ? v : null);
  });

  els.board.addEventListener('pointerup', (e) => {
    if (ui.stroke) { if (e.pointerId === ui.stroke.id) endStroke(); return; }
    const d = ui.down;
    ui.down = null;
    if (!d || e.pointerId !== d.id) return;
    if (d.moved) {
      const v = ui.dropV;
      ui.drag = null;
      setDrop(null);
      if (v === null) { render(); return; }
      if (S.phase === 'setup') {
        pushUndo();
        S.setup[d.a].pos = v;
        commit();
      } else if (!applyMove(d.a, v)) {
        render();
      }
      return;
    }
    handleClick(d);
  });

  els.board.addEventListener('pointercancel', () => {
    endStroke();
    ui.down = null;
    if (ui.drag) { ui.drag = null; setDrop(null); render(); }
  });

  function handleClick(d) {
    if (ui.replay !== null) return;
    const el = d.el;
    if (!el) {
      if (ui.selected !== null) { ui.selected = null; render(); }
      return;
    }
    const a = d.a;
    let v = el.dataset.v !== undefined ? Number(el.dataset.v) : null;
    if (a !== null) v = ui.view.pos[a];

    if (S.phase === 'setup') setupClick(a, v);
    else if (S.phase === 'move') moveClick(a, v);
  }

  function setupClick(a, v) {
    if (v === null) return;
    const here = agentsAt(v, S.setup.map((x) => x.pos));
    if (ui.tool === 'addK' || ui.tool === 'addI') {
      if (S.setup.length >= MAX_AGENTS) { toast(`At most ${MAX_AGENTS} agents`); return; }
      pushUndo();
      S.setup.push({ pos: v, know: ui.tool === 'addK' });
    } else {
      const target = a !== null ? a : here[0];
      if (target === undefined) return;
      pushUndo();
      if (ui.tool === 'toggle') S.setup[target].know = !S.setup[target].know;
      else S.setup.splice(target, 1);
    }
    syncCountInputs();
    commit();
  }

  function moveClick(a, v) {
    const sel = ui.selected, view = ui.view;
    if (sel !== null && a !== sel && v !== null && view.targets.has(v)) { applyMove(sel, v); return; }
    if (a !== null) {
      ui.selected = a === sel ? null : a;
      render();
      return;
    }
    const here = v === null ? [] : agentsAt(v, view.pos);
    if (!here.length) {
      if (sel !== null) { ui.selected = null; render(); }
      return;
    }
    ui.selected = here[(here.indexOf(sel) + 1) % here.length];
    render();
  }

  // ---------------------------------------------------------------- wiring

  for (const b of $$('[data-tool]')) {
    b.addEventListener('click', () => { ui.tool = b.dataset.tool; render(); });
  }
  btn.start.addEventListener('click', startGame);

  btn.treeUndo.addEventListener('click', undo);
  btn.treeClear.addEventListener('click', () => setTree([]));
  btn.treeAll.addEventListener('click', () => setTree(G.edges.map((e) => e.id)));
  btn.treeRandom.addEventListener('click', () => setTree(randomTree()));
  btn.treeFill.addEventListener('click', () => setTree(fillTree(S.tree)));
  btn.treeLast.addEventListener('click', () => { const t = lastTree(); if (t) setTree(t); });
  btn.treeConfirm.addEventListener('click', confirmTree);

  btn.moveUndo.addEventListener('click', undo);
  btn.moveReset.addEventListener('click', resetMoves);
  btn.moveRetree.addEventListener('click', redrawTree);
  btn.moveEnd.addEventListener('click', endRound);

  btn.doneReplay.addEventListener('click', () => enterReplay(0));
  btn.doneSetup.addEventListener('click', () => confirmDiscard(btn.doneSetup));

  btn.rpFirst.addEventListener('click', () => setReplay(0));
  btn.rpPrev.addEventListener('click', () => setReplay(ui.replay - 1));
  btn.rpPlay.addEventListener('click', togglePlay);
  btn.rpNext.addEventListener('click', () => setReplay(ui.replay + 1));
  btn.rpLast.addEventListener('click', () => setReplay(S.history.length - 1));
  els.rpSlider.addEventListener('input', () => setReplay(Number(els.rpSlider.value)));
  btn.rpResume.addEventListener('click', () => armed(btn.rpResume, 'Discard later steps?', resumeFromReplay));
  btn.rpExit.addEventListener('click', exitReplay);

  els.inRows.addEventListener('change', () => {
    const rows = clampInt(els.inRows.value, 1, MAX_ROWS, S.rows);
    els.inRows.value = rows;
    setSize(rows, S.n);
  });
  els.inN.addEventListener('change', () => {
    const n = clampInt(els.inN.value, 2, MAX_COLS, S.n);
    els.inN.value = n;
    setSize(S.rows, n);
  });
  els.inM.addEventListener('change', () => {
    els.inM.value = clampInt(els.inM.value, 1, MAX_AGENTS, 5);
    els.inK.value = Math.min(Number(els.inK.value) || 0, Number(els.inM.value));
  });
  els.inK.addEventListener('change', () => {
    els.inK.value = clampInt(els.inK.value, 0, Number(els.inM.value) || 1, 1);
  });
  btn.randomPlace.addEventListener('click', () => {
    const m = clampInt(els.inM.value, 1, MAX_AGENTS, 5);
    placeRandom(m, clampInt(els.inK.value, 0, m, 1));
  });
  btn.clearAgents.addEventListener('click', () => {
    if (!S.setup.length) return;
    pushUndo();
    S.setup = [];
    syncCountInputs();
    commit();
  });
  els.inSteps.addEventListener('change', () => {
    S.rules.steps = clampInt(els.inSteps.value, 1, MAX_STEPS, 1);
    commit();
  });
  for (const r of [els.exEnd, els.exLand]) {
    r.addEventListener('change', () => { if (r.checked) { S.rules.exchange = r.value; commit(); } });
  }
  btn.backSetup.addEventListener('click', () => confirmDiscard(btn.backSetup));

  els.history.addEventListener('click', (e) => {
    const b = e.target.closest('[data-i]');
    if (b) enterReplay(Number(b.dataset.i));
  });
  btn.replay.addEventListener('click', () => enterReplay(0));

  btn.copy.addEventListener('click', () => {
    const text = exportJSON();
    const fallback = () => openDialog('export', text);
    try {
      navigator.clipboard.writeText(text).then(() => toast('Game copied as JSON'), fallback);
    } catch {
      fallback();
    }
  });

  let topLevel = false;
  try { topLevel = window.self === window.top; } catch { topLevel = false; }
  btn.download.hidden = !topLevel;
  btn.download.addEventListener('click', () => {
    const url = URL.createObjectURL(new Blob([exportJSON()], { type: 'application/json' }));
    const a = document.createElement('a');
    a.href = url;
    a.download = `grid-broadcast-${S.rows}x${S.n}-${new Date().toISOString().slice(0, 16).replace(/[:T]/g, '-')}.json`;
    document.body.append(a);
    a.click();
    a.remove();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
  });

  function openDialog(mode, text = '') {
    const exp = mode === 'export';
    els.dlg.dataset.mode = mode;
    els.dlgTitle.textContent = exp ? 'Game JSON' : 'Load a saved game';
    els.dlgHint.textContent = exp
      ? 'Copy this text and keep it somewhere safe. Load it later to pick up where you left off.'
      : 'Choose a JSON file saved from Grid Broadcast (or the earlier Ladder Broadcast), or paste its contents below. Loading replaces the current game.';
    els.dlgFile.hidden = exp;
    els.dlgFile.value = '';
    els.dlgOk.hidden = exp;
    els.dlgText.readOnly = exp;
    els.dlgText.value = text;
    els.dlgError.hidden = true;
    els.dlg.showModal();
    if (exp) { els.dlgText.focus(); els.dlgText.select(); }
  }

  btn.load.addEventListener('click', () => openDialog('load'));
  $('#dlg-cancel').addEventListener('click', () => els.dlg.close());
  els.dlgForm.addEventListener('submit', (e) => {
    e.preventDefault();
    if (els.dlg.dataset.mode !== 'load') { els.dlg.close(); return; }
    const err = importJSON(els.dlgText.value);
    if (err) {
      els.dlgError.textContent = err;
      els.dlgError.hidden = false;
    } else {
      els.dlg.close();
      toast('Game loaded');
    }
  });
  els.dlgFile.addEventListener('change', async () => {
    const f = els.dlgFile.files[0];
    if (!f) return;
    els.dlgText.value = await f.text();
    els.dlgForm.requestSubmit();
  });

  document.addEventListener('keydown', (e) => {
    if (els.dlg.open || e.target.closest('input, textarea, select')) return;
    const mod = e.ctrlKey || e.metaKey;
    if (mod && e.key.toLowerCase() === 'z') { e.preventDefault(); undo(); return; }
    if (e.key === 'Escape') {
      if (ui.selected !== null) { ui.selected = null; render(); }
      else if (ui.replay !== null) exitReplay();
      return;
    }
    if (ui.replay !== null) {
      if (e.key === 'ArrowLeft') { e.preventDefault(); setReplay(ui.replay - 1); }
      else if (e.key === 'ArrowRight') { e.preventDefault(); setReplay(ui.replay + 1); }
      else if (e.key === 'Home') { e.preventDefault(); setReplay(0); }
      else if (e.key === 'End') { e.preventDefault(); setReplay(S.history.length - 1); }
      else if (e.key === ' ' && !e.target.closest('button')) { e.preventDefault(); togglePlay(); }
      return;
    }
    // A button reached by keyboard keeps its own Enter; one that was merely clicked does not.
    const b = e.target.closest('button');
    if (mod || e.altKey || (b && b.matches(':focus-visible'))) return;
    if (e.key === 'Enter') {
      e.preventDefault();
      if (S.phase === 'tree') confirmTree();
      else if (S.phase === 'move') endRound();
    } else if ((e.key === 'r' || e.key === 'R') && S.phase === 'tree') {
      setTree(randomTree());
    }
  });

  // ---------------------------------------------------------------- boot

  S = loadStored() || sampleState();
  buildBoard();
  syncCountInputs();
  render();
})();
