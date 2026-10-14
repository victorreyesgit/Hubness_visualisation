// ================= MATH =================
// Area of disk(0,r) ∩ [0,a]x[0,b]
function quad(a, b, r) {
  a = Math.min(a, r); b = Math.min(b, r);
  if (a * a + b * b <= r * r) return a * b;
  const u0 = Math.sqrt(r * r - b * b);
  const G = u => 0.5 * (u * Math.sqrt(Math.max(r * r - u * u, 0)) + r * r * Math.asin(Math.min(u / r, 1)));
  return b * u0 + G(a) - G(u0);
}
const S = (a, b, r) => (a < 0 ? -1 : 1) * (b < 0 ? -1 : 1) * quad(Math.abs(a), Math.abs(b), r);
// Exact area of disk(c, r) ∩ [-1,1]^2
function area(cx, cy, r) {
  if (r <= 0) return 0;
  const x1 = -1 - cx, x2 = 1 - cx, y1 = -1 - cy, y2 = 1 - cy;
  return S(x2, y2, r) - S(x1, y2, r) - S(x2, y1, r) + S(x1, y1, r);
}
// Closeness C(x; c): mass of the ball centred at c with radius |x-c|
const C = (x, y, cx, cy) => Math.min(1, Math.max(0, area(cx, cy, Math.hypot(x - cx, y - cy)) / 4));

// Regularised incomplete beta (Numerical Recipes) -> exact binomial CDF, fast for any N
function lgam(z) {
  const c = [76.18009172947146, -86.50532032941677, 24.01409824083091, -1.231739572450155, 0.1208650973866179e-2, -0.5395239384953e-5];
  let y = z, t = z + 5.5; t -= (z + 0.5) * Math.log(t);
  let s = 1.000000000190015; for (const v of c) s += v / ++y;
  return -t + Math.log(2.5066282746310005 * s / z);
}
function betacf(a, b, x) {
  const F = 1e-300, qab = a + b, qap = a + 1, qam = a - 1;
  let c = 1, d = 1 - qab * x / qap; if (Math.abs(d) < F) d = F; d = 1 / d; let h = d;
  for (let m = 1; m <= 500; m++) {
    const m2 = 2 * m;
    let aa = m * (b - m) * x / ((qam + m2) * (a + m2));
    d = 1 + aa * d; if (Math.abs(d) < F) d = F; c = 1 + aa / c; if (Math.abs(c) < F) c = F; d = 1 / d; h *= d * c;
    aa = -(a + m) * (qab + m) * x / ((a + m2) * (qap + m2));
    d = 1 + aa * d; if (Math.abs(d) < F) d = F; c = 1 + aa / c; if (Math.abs(c) < F) c = F; d = 1 / d;
    const del = d * c; h *= del; if (Math.abs(del - 1) < 1e-12) break;
  }
  return h;
}
function betai(x, a, b) {
  if (x <= 0) return 0; if (x >= 1) return 1;
  const bt = Math.exp(lgam(a + b) - lgam(a) - lgam(b) + a * Math.log(x) + b * Math.log(1 - x));
  return x < (a + 1) / (a + b + 2) ? bt * betacf(a, b, x) / a : 1 - bt * betacf(b, a, 1 - x) / b;
}
// P(Binomial(n,p) <= m)
const binCdf = (m, n, p) => m >= n ? 1 : m < 0 ? 0 : betai(1 - p, n - m, m + 1);
// N^{k:N}(x;c) given closeness p: x is among the k nearest of c, with N-1 other points
const Nk = (p, k, N) => binCdf(k - 1, N - 1, p);

// ================= STATE / UI =================
const $ = id => document.getElementById(id), W = 440, MG = 32, SQ = W - 2 * MG;  // canvas size, margin around the square, square side
const st = { N: 1000, k: 30, p: [0.3, 0.2], q: [-0.5, -0.4], two: false, role: 'x', res: 150, ores: 100, order: false, mode: 'explore' };
const fmt = v => (v === undefined || !isFinite(v)) ? '–' : v.toPrecision(3);
const VIR = ['#440154', '#46327e', '#365c8d', '#277f8e', '#1fa187', '#4ac16d', '#9fda3a', '#fde725'];
const MAG = ['#000004', '#251255', '#721f81', '#b63679', '#f1605d', '#fec287', '#fcfdbf'];
const VIRR = [...VIR].reverse(), MAGR = [...MAG].reverse();   // viridis_r, magma_r
const hex = s => [1, 3, 5].map(i => parseInt(s.substr(i, 2), 16));
function cmap(stops) {
  const a = stops.map(hex);
  return t => { t = Math.min(1, Math.max(0, t)) * (a.length - 1); const i = Math.min(Math.floor(t), a.length - 2), f = t - i;
    return a[i].map((v, m) => v + (a[i + 1][m] - v) * f); };
}
function mkPanel(parent, stops, f, isCl) {
  const el = document.createElement('div'); el.className = 'panel';
  el.innerHTML = `<h3></h3><div class="sub"></div><canvas width="${W}" height="${W}"></canvas><div class="bar" style="background:linear-gradient(90deg,${stops.join(',')})"></div><div class="sc"><span></span><span></span></div><div class="hov">&nbsp;</div>`;
  parent.appendChild(el);
  const s = el.querySelectorAll('.sc span');
  return { f, isCl, cm: cmap(stops), cv: el.querySelector('canvas'), off: document.createElement('canvas'),
    h: el.querySelector('h3'), sub: el.querySelector('.sub'), lo_: s[0], hi_: s[1], hov: el.querySelector('.hov') };
}
function paint(p) {
  const R = p.R; p.off.width = p.off.height = R;
  const ctx = p.off.getContext('2d'), img = ctx.createImageData(R, R), rng = (p.hi - p.lo) || 1;
  for (let i = 0; i < R * R; i++) {
    const z = p.v[i], o = i * 4;
    if (z !== z) { img.data[o] = img.data[o + 1] = img.data[o + 2] = 200; img.data[o + 3] = 120; continue; }
    const c = p.cm((z - p.lo) / rng); img.data[o] = c[0]; img.data[o + 1] = c[1]; img.data[o + 2] = c[2]; img.data[o + 3] = 255;
  }
  ctx.putImageData(img, 0, 0);
}
function show(p, marker) {
  const g = p.cv.getContext('2d'), mut = getComputedStyle(document.documentElement).getPropertyValue('--mut').trim() || '#667186';
  g.clearRect(0, 0, W, W); g.imageSmoothingEnabled = true; g.drawImage(p.off, MG, MG, SQ, SQ);
  g.strokeStyle = mut; g.lineWidth = 1.5; g.strokeRect(MG, MG, SQ, SQ);          // the domain: the square [-1,1]^2
  g.fillStyle = mut; g.font = '12px system-ui,sans-serif'; g.textAlign = 'center'; g.textBaseline = 'top';
  [[-1, '−1'], [0, '0'], [1, '1']].forEach(([v, t]) => { const X = MG + (v + 1) / 2 * SQ; g.fillText(t, X, MG + SQ + 7); g.beginPath(); g.moveTo(X, MG + SQ); g.lineTo(X, MG + SQ + 4); g.stroke(); });
  g.textAlign = 'right'; g.textBaseline = 'middle';
  [[-1, '−1'], [0, '0'], [1, '1']].forEach(([v, t]) => { const Y = MG + (1 - v) / 2 * SQ; g.fillText(t, MG - 8, Y); g.beginPath(); g.moveTo(MG, Y); g.lineTo(MG - 4, Y); g.stroke(); });
  if (marker) drawMarkers(g);
  p.lo_.textContent = p.lo === undefined ? '' : +p.lo.toPrecision(3); p.hi_.textContent = p.hi === undefined ? '' : +p.hi.toPrecision(3);
}
const xPt = () => (st.role === 'x' || !st.two) ? st.p : st.q, cPt = () => st.role === 'c' ? st.p : st.q;
function drawMarkers(g) {
  const cP = cPt(), xP = xPt(), X = v => MG + (v[0] + 1) / 2 * SQ, Y = v => MG + (1 - v[1]) / 2 * SQ;
  if (st.two) {                                                                    // ball centred at c reaching x
    g.save(); g.beginPath(); g.rect(MG, MG, SQ, SQ); g.clip();
    g.setLineDash([5, 4]); g.beginPath(); g.arc(X(cP), Y(cP), Math.hypot(xP[0] - cP[0], xP[1] - cP[1]) * SQ / 2, 0, 7);
    g.strokeStyle = 'rgba(0,0,0,.35)'; g.lineWidth = 3; g.stroke(); g.strokeStyle = '#fff'; g.lineWidth = 1.5; g.stroke(); g.restore();
  }
  [[st.p, st.role === 'c' ? '#e5253d' : '#111', st.role, true], [st.q, st.role === 'c' ? '#111' : '#e5253d', st.role === 'c' ? 'x' : 'c', false]].forEach(([v, col, l, main]) => {
    if (!main && !st.two) return;
    g.beginPath(); g.arc(X(v), Y(v), main ? 5.5 : 3.5, 0, 7); g.fillStyle = col; g.fill(); g.lineWidth = main ? 2.5 : 2; g.strokeStyle = '#fff'; g.stroke();
    g.font = 'bold 12px system-ui,sans-serif'; g.textAlign = 'left'; g.textBaseline = 'bottom'; g.lineWidth = 3; g.strokeStyle = 'rgba(255,255,255,.9)';
    g.strokeText(l, X(v) + 8, Y(v) - 5); g.fillStyle = col; g.fillText(l, X(v) + 8, Y(v) - 5);
  });
}
function compute(p) {
  const R = st.res, v = new Float32Array(R * R); let lo = Infinity, hi = -Infinity;
  for (let j = 0; j < R; j++) for (let i = 0; i < R; i++) {
    let z = p.f(-1 + (i + .5) * 2 / R, 1 - (j + .5) * 2 / R);
    if (p.isCl && st.order) z = 1 + (st.N - 1) * z;
    v[j * R + i] = z; if (z < lo) lo = z; if (z > hi) hi = z;
  }
  if (p.fix) { lo = (p.isCl && st.order) ? 1 : 0; hi = (p.isCl && st.order) ? st.N : 1; }
  Object.assign(p, { v, lo, hi, R }); paint(p);
}

// Role c: pixel = x, point = c. Role x: pixel = c, point = x.
const clos = (u, v) => st.role === 'c' ? C(u, v, st.p[0], st.p[1]) : C(st.p[0], st.p[1], u, v);
const panels = [mkPanel($('grid'), VIRR, clos, 1), mkPanel($('grid'), VIR, (u, v) => Nk(clos(u, v), st.k, st.N), 0)];
const TT = {
  c: [['Closeness C(x; c)', 'Mass of the ball around c that reaches x. Map over every x.'],
      ['Probability N<sup>k:N</sup>(x; c)', 'Chance that x is among the k nearest neighbours of c. Map over every x.']],
  x: [['Reverse closeness C(x; c)', 'Closeness of x as seen from each possible c. Map over every c.'],
      ['Reverse probability N<sup>k:N</sup>(x; c)', 'Chance that x is a k-neighbour of c. N times its mean is O(x).']]
};
const HINT1 = { c: 'The point is the reference c. Maps show how every x relates to it.',
                x: 'The point is the target x. Maps show how x is seen from every possible c.' };
const HINT = { c: 'The large point is the reference c; the small one is x. Maps show how every x relates to c.',
               x: 'The large point is the target x; the small one is c. Maps show how x is seen from every possible c.' };
let raf = 0;
function refresh() {
  if (raf) return;
  raf = requestAnimationFrame(() => {
    raf = 0;
    panels.forEach((p, i) => { p.h.innerHTML = TT[st.role][i][0]; p.sub.innerHTML = TT[st.role][i][1]; compute(p); show(p, true); });
    $('hint').textContent = (st.two ? HINT : HINT1)[st.role]; $('twoL').textContent = st.role === 'c' ? 'x' : 'c';
    const f2 = v => v.map(t => t.toFixed(2)).join(', '), xp = xPt(), cp = cPt(), v = panels[1].v;
    $('pos').innerHTML = st.two ? `x (${f2(xp)})<br>c (${f2(cp)})` : `${st.role} (${f2(st.p)})`;
    panels[0].hov.style.display = st.two ? '' : 'none';
    if (st.two) panels[0].hov.innerHTML = `<b>C(x; c) = ${C(xp[0], xp[1], cp[0], cp[1]).toFixed(4)}</b>`;
    $('oval').textContent = st.role === 'x' ? fmt(st.N * v.reduce((a, b) => a + b, 0) / v.length)
      : st.two ? fmt(oAt(xp[0], xp[1], Array.from({ length: 60 }, (_, i) => -1 + (i + .5) / 30))) : '–';
  });
}
const toDom = e => { const r = e.target.getBoundingClientRect(), cl = t => Math.max(-1, Math.min(1, t));
  return [cl(((e.clientX - r.left) / r.width * W - MG) / SQ * 2 - 1), cl(1 - ((e.clientY - r.top) / r.height * W - MG) / SQ * 2)]; };
function hover(p, e) {
  if (!p.v) return; const [u, v] = toDom(e), i = Math.min(p.R - 1, Math.floor((u + 1) / 2 * p.R)), j = Math.min(p.R - 1, Math.floor((1 - v) / 2 * p.R));
  p.hov.textContent = `(${u.toFixed(2)}, ${v.toFixed(2)}) → ${fmt(p.v[j * p.R + i])}`;
}
let drag = false;
panels.forEach(p => {
  p.fix = true; if (p !== panels[0]) p.hov.style.display = 'none'; else { p.hov.classList.add('val'); p.hov.style.display = 'none'; }
  const move = e => { st[drag] = toDom(e); resetSim(); refresh(); };
  p.cv.addEventListener('pointerdown', e => {
    const m = toDom(e), d = t => Math.hypot(t[0] - m[0], t[1] - m[1]);
    drag = (!st.two || d(st.p) <= d(st.q)) ? 'p' : 'q'; p.cv.setPointerCapture(e.pointerId); move(e);   // grab the nearest of the two points
  });
  p.cv.addEventListener('pointermove', e => { if (drag) move(e); });
  p.cv.addEventListener('pointerup', () => drag = null);
});

// ================= k-OCCURRENCE MAP (all x) =================
const op = mkPanel($('ogrid'), VIR, null, 0);
op.h.innerHTML = 'Expected k-occurrence O<sup>k:N</sup>(x)'; op.sub.textContent = 'Expected number of times each x appears in the k-neighbourhood of the other points.';
op.cv.addEventListener('pointermove', e => hover(op, e));
op.cv.addEventListener('pointerleave', () => op.hov.innerHTML = '&nbsp;');
let job = 0;
function startO() {
  const id = ++job, R = st.ores, H = Math.ceil(R / 2), M = R, h = 2 / R;
  const cs = Array.from({ length: M }, (_, i) => -1 + (i + .5) * 2 / M), Vf = new Float32Array(H * H).fill(NaN), tasks = [];
  for (let a = 0; a < H; a++) for (let b = a; b < H; b++) tasks.push([a, b]);
  let n = 0;
  (function step() {
    if (id !== job) return;
    const t0 = performance.now();
    while (n < tasks.length && performance.now() - t0 < 12) {
      const [a, b] = tasks[n++]; Vf[a * H + b] = oAt(-1 + (a + .5) * h, -1 + (b + .5) * h, cs);
    }
    let lo = Infinity, hi = -Infinity; for (const z of Vf) if (z === z) { if (z < lo) lo = z; if (z > hi) hi = z; }
    const v = new Float32Array(R * R);
    for (let j = 0; j < R; j++) for (let i = 0; i < R; i++) {
      const fi = Math.min(i, R - 1 - i), fj = Math.min(j, R - 1 - j);
      v[j * R + i] = Vf[Math.min(fi, fj) * H + Math.max(fi, fj)];
    }
    Object.assign(op, { v, lo, hi, R }); paint(op); show(op, false);
    $('oP').textContent = n < tasks.length ? `computing… ${Math.round(100 * n / tasks.length)}%` : 'done';
    if (n < tasks.length) requestAnimationFrame(step);
  })();
}
// O(x) = N * mean over c of N^{k:N}(x;c), midpoint rule on the grid cs x cs
function oAt(x, y, cs) {
  let s = 0; for (let j = 0; j < cs.length; j++) for (let i = 0; i < cs.length; i++) s += Nk(C(x, y, cs[i], cs[j]), st.k, st.N);
  return st.N * s / (cs.length * cs.length);
}

// ================= SIMULATION =================
let sim = null;
function resetSim() { if (sim) { sim.stop = true; sim = null; $('simT').textContent = 'Point or parameters changed. Press Simulate.'; hist([], 0); } }
function hist(r, theory) {
  const cv = $('hist'), g = cv.getContext('2d'); g.clearRect(0, 0, cv.width, cv.height);
  if (!r.length) return;
  const lo = Math.min(...r), hi = Math.max(...r), nb = hi - lo + 1, cnt = new Array(nb).fill(0);
  r.forEach(v => cnt[v - lo]++); const mx = Math.max(...cnt), bw = cv.width / nb;
  g.fillStyle = '#21908d'; cnt.forEach((c, i) => g.fillRect(i * bw, cv.height - c / mx * (cv.height - 8), Math.max(bw - 1, 1), c / mx * (cv.height - 8)));
  const tx = (theory - lo + .5) * bw; g.strokeStyle = '#e5253d'; g.lineWidth = 2; g.beginPath(); g.moveTo(tx, 0); g.lineTo(tx, cv.height); g.stroke();
}
$('simB').onclick = () => {
  if (sim) sim.stop = true;
  const s = sim = { stop: false, r: [] }, E = Math.max(1, +$('E').value || 200), { N, k } = st, [x0, y0] = xPt();
  const cs = Array.from({ length: 100 }, (_, i) => -1 + (i + .5) / 50), theory = oAt(x0, y0, cs);
  (function step() {
    if (s.stop) return;
    const t0 = performance.now();
    while (s.r.length < E && performance.now() - t0 < 12) {
      const px = new Float64Array(N), py = new Float64Array(N); let occ = 0;
      for (let i = 0; i < N; i++) { px[i] = Math.random() * 2 - 1; py[i] = Math.random() * 2 - 1; }
      for (let i = 0; i < N; i++) {
        const d = (px[i] - x0) ** 2 + (py[i] - y0) ** 2; let c = 0;
        for (let j = 0; j < N; j++) if (j !== i && (px[j] - px[i]) ** 2 + (py[j] - py[i]) ** 2 < d && ++c >= k) break;
        if (c < k) occ++;
      }
      s.r.push(occ);
    }
    const n = s.r.length, mean = s.r.reduce((a, b) => a + b, 0) / n, vr = n > 1 ? s.r.reduce((a, b) => a + (b - mean) ** 2, 0) / (n - 1) : 0;
    $('simT').innerHTML = `${n}/${E} experiments · empirical mean <b>${mean.toFixed(2)}</b>, variance ${vr.toFixed(2)}, max ${Math.max(...s.r)} · theory (red line) <b>${theory.toFixed(2)}</b>`;
    hist(s.r, theory);
    if (n < E) requestAnimationFrame(step);
  })();
};

// ================= DISCRETE EXPERIMENT =================
const dp = mkPanel($('dgrid'), VIR, null, 0), dbar = dp.cv.parentElement.querySelector('.bar'), dsc = dp.cv.parentElement.querySelector('.sc');
dp.h.textContent = 'Counters start at 0';
let disc = null; st.spd = 1;
// seconds per point: 1st slow, 2nd faster, 3rd faster, then quick enough that the whole run stays under ~25 s
const dur = (pos, d) => d.skip ? 0 : (pos === 0 ? 5 : pos === 1 ? 2 : pos === 2 ? 1 : Math.min(0.5, 17 / Math.max(1, d.N - 3))) / st.spd;
function knn(d, i) {
  const { P, N, k } = d, q = P[i], dist = new Float64Array(N);
  for (let j = 0; j < N; j++) dist[j] = (P[j][0] - q[0]) ** 2 + (P[j][1] - q[1]) ** 2;
  dist[i] = Infinity;
  const o = Array.from({ length: N }, (_, j) => j).sort((a, b) => dist[a] - dist[b]).slice(0, k);
  d.rad = Math.sqrt(dist[o[k - 1]]); return o;
}
function startDisc() {
  const N = Math.min(st.N, 2000), k = Math.min(st.k, N - 1), B = Math.max(3, Math.round(Math.sqrt(N) / 1.5));
  const P = Array.from({ length: N }, () => [Math.random() * 2 - 1, Math.random() * 2 - 1]);
  const bandOf = i => Math.floor((1 - P[i][1]) / 2 * B);   // rows, top to bottom; left to right inside a row
  const order = P.map((_, i) => i).sort((a, b) => bandOf(a) - bandOf(b) || P[a][0] - P[b][0]);
  disc = { N, k, P, order, cnt: new Int32Array(N), pos: 0, nb: null, rev: 0, t0: performance.now(), done: false, skip: false, running: false,
           key: st.N + '-' + st.k, r: Math.min(14, Math.max(2.5, 160 / Math.sqrt(N))) };
  $('dnote').textContent = st.N > 2000 ? `Showing 2000 of ${st.N} points (the discrete view is capped for speed).` : (st.k > N - 1 ? `k reduced to ${k}.` : '');
  dbar.style.visibility = dsc.style.visibility = 'hidden';
  discLoop();
}
function discLoop() {
  const d = disc; if (!d || d.done || d.running || st.mode !== 'disc') return; d.running = true;
  (function frame() {
    if (disc !== d || st.mode !== 'disc') { d.running = false; return; }
    const now = performance.now();
    while (!d.done && performance.now() - now < 12) {
      const i = d.order[d.pos];
      if (!d.nb) { d.nb = knn(d, i); d.rev = 0; }
      const D = dur(d.pos, d) * 1000, f = D <= 0 ? 1 : Math.min(1, (now - d.t0) / D), show = Math.ceil(Math.min(1, f / 0.7) * d.k);
      while (d.rev < show) d.cnt[d.nb[d.rev++]]++;
      if (f < 1) break;
      d.t0 += D; d.pos++; d.nb = null; d.rev = 0; if (d.pos >= d.N) d.done = true;
    }
    drawDisc(d);
    if (d.done) d.running = false; else requestAnimationFrame(frame);
  })();
}
function drawDisc(d) {
  const o = dp.off; o.width = o.height = SQ; const g = o.getContext('2d'), { P, N, k, cnt, r } = d;
  g.fillStyle = getComputedStyle(document.documentElement).getPropertyValue('--field').trim() || '#f5f7fa'; g.fillRect(0, 0, SQ, SQ);
  const X = p => (p[0] + 1) / 2 * SQ, Y = p => (1 - p[1]) / 2 * SQ, cur = d.done ? -1 : d.order[d.pos], green = new Set(d.nb ? d.nb.slice(0, d.rev) : []);
  let lo = Infinity, hi = -Infinity, zero = 0; for (const c of cnt) { if (c < lo) lo = c; if (c > hi) hi = c; if (c === 0) zero++; }
  if (cur >= 0 && d.nb) {
    g.strokeStyle = 'rgba(47,191,113,.9)'; g.lineWidth = 1.5; g.setLineDash([5, 4]); g.beginPath(); g.arc(X(P[cur]), Y(P[cur]), d.rad * SQ / 2, 0, 7); g.stroke(); g.setLineDash([]);
    if (k <= 40) { g.strokeStyle = 'rgba(47,191,113,.7)'; g.beginPath(); green.forEach(j => { g.moveTo(X(P[cur]), Y(P[cur])); g.lineTo(X(P[j]), Y(P[j])); }); g.stroke(); }
  }
  g.font = `600 ${Math.round(r * 1.15)}px system-ui,sans-serif`; g.textAlign = 'center'; g.textBaseline = 'middle';
  for (let t = 0; t <= N; t++) {                          // t = N draws the reference point again, on top
    const i = t < N ? t : cur;
    if (i < 0 || (t < N && i === cur)) continue;
    let fill = '#c3ccd8', txt = '#1b2333';
    if (d.done) { const col = dp.cm((cnt[i] - lo) / ((hi - lo) || 1)); fill = `rgb(${col.map(Math.round)})`; txt = (.299 * col[0] + .587 * col[1] + .114 * col[2]) < 140 ? '#fff' : '#111'; }
    else if (green.has(i)) fill = '#2fbf71';
    if (i === cur) { fill = '#e5253d'; txt = '#fff'; }
    g.beginPath(); g.arc(X(P[i]), Y(P[i]), r, 0, 7); g.fillStyle = fill; g.fill();
    g.lineWidth = i === cur ? 3 : 1; g.strokeStyle = i === cur ? '#111' : 'rgba(0,0,0,.3)'; g.stroke();
    if (r >= 8) { g.fillStyle = txt; g.fillText(cnt[i], X(P[i]), Y(P[i]) + 1); }
  }
  if (d.done) {
    Object.assign(dp, { lo, hi }); dbar.style.visibility = dsc.style.visibility = 'visible';
    dp.h.textContent = 'Result: k-occurrence of each point';
    dp.sub.innerHTML = `Every point sent ${k} votes, so the mean count is exactly ${k}. Hubs reach ${hi}; ${zero} point${zero === 1 ? ' was' : 's were'} never chosen (anti-hubs).`;
  } else {
    dp.h.textContent = 'Counters start at 0';
    dp.sub.innerHTML = `Point ${d.pos + 1} of ${N}: its ${k} nearest neighbours turn green and get +1.`;
  }
  show(dp, false);
}
$('dRep').onclick = startDisc;
$('dSkip').onclick = () => { if (disc && !disc.done) { disc.skip = true; discLoop(); } };
$('spd').onchange = e => st.spd = +e.target.value;

// ================= CONTROLS =================
function syncUI() {
  $('nS').value = Math.log(st.N / 10) / Math.log(1000) * 1000; $('nI').value = st.N;
  $('kS').value = Math.log(st.k) / Math.log(st.N) * 1000; $('kI').value = st.k; $('kI').max = st.N;
}
function paramsChanged() { syncUI(); resetSim(); st.mode === 'explore' ? refresh() : st.mode === 'omap' ? startO() : startDisc(); }
const setN = n => { st.N = Math.max(10, Math.min(10000, Math.round(n) || 10)); st.k = Math.min(st.k, st.N); paramsChanged(); };
const setK = k => { st.k = Math.max(1, Math.min(st.N, Math.round(k) || 1)); paramsChanged(); };
$('nS').oninput = e => setN(10 * Math.pow(1000, e.target.value / 1000));
$('kS').oninput = e => setK(Math.pow(st.N, e.target.value / 1000));
$('nI').onchange = e => setN(+e.target.value); $('kI').onchange = e => setK(+e.target.value);
$('rS').oninput = e => { st.res = +e.target.value; $('rV').textContent = st.res; refresh(); };
$('oS').oninput = e => { st.ores = +e.target.value; $('oV').textContent = st.ores; startO(); };
$('two').onchange = e => { st.two = e.target.checked; resetSim(); refresh(); };
$('ord').onchange = e => { st.order = e.target.checked; refresh(); };
document.querySelectorAll('.seg button').forEach(b => b.onclick = () => {
  st.role = b.dataset.r; document.querySelectorAll('.seg button').forEach(o => o.classList.toggle('on', o === b)); refresh();
});
function mode(m) {
  st.mode = m;
  [['disc', 'tD'], ['explore', 'tE'], ['omap', 'tO']].forEach(([s, t]) => { $(s).classList.toggle('hide', s !== m); $(t).classList.toggle('on', s === m); });
  $('pointBox').classList.toggle('hide', m !== 'explore');
  if (m === 'explore') refresh();
  else if (m === 'omap') startO();
  else if (!disc || disc.key !== st.N + '-' + st.k) startDisc();
  else { disc.t0 = performance.now(); drawDisc(disc); discLoop(); }
}
$('tD').onclick = () => mode('disc'); $('tE').onclick = () => mode('explore'); $('tO').onclick = () => mode('omap');
syncUI(); mode('disc');
