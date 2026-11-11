-- Prove2me | Theorems.Thm_NodeStableProj_Main_lemma_3_3_stability
-- name    : NodeStableProj.Main.lemma_3_3_stability
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:59:15.735895+00:00
-- url     : https://prove2.me/theorems/9c938c68-46e2-4a72-9dec-a0b594e6c32a
-- title:
--   Lemma 3.3 item 3 — P_{D,D̂,ε̃} is (ε, δ)-distributionally node-stable on n-node graphs when D̂ − D ≥ 2c₁ log(9n/δ)/ε̃ and ε ≤ 1
-- statement:
--   Let $c_1>0$ be a constant for which Lemma 3.6 holds. Let $0<D<\hat D$ be integers, $\tilde\varepsilon>0$, $\delta\in(0,1)$ and $n\in\mathbb N$, and suppose
--   $$\hat D-D\ \ge\ \frac{2c_1\log(9n/\delta)}{\tilde\varepsilon},\qquad \varepsilon=\tilde\varepsilon\sqrt{2\hat D\ln(3/\delta)}+\hat D\,\tilde\varepsilon\,\frac{e^{\tilde\varepsilon}-1}{e^{\tilde\varepsilon}+1}\ \le\ 1 .$$
--   Then for every fallback rule, $\mathcal P_{D,\hat D,\tilde\varepsilon}$ is $(\varepsilon,\delta)$-distributionally node-stable on $n$-node graphs: for all fixed-vertex node-neighbouring $n$-node graphs $G,G'$ with differing node $v^*$, $\mathcal P(G)_{-v^*}\approx_{\varepsilon,\delta}\mathcal P(G')_{-v^*}$.
--
--   This is the core privacy guarantee of the projection; Theorem 3.5 calls it on the padded graph. The closing sentence of item 3 is the companion item `lemma_3_3_simplification`.
--
--   Differences from the source:
--   - reading: "Let c1 > 0 be the constant from Lemma 3.6" → every c1 > 0 with SVTAccuracy c1 (the conclusion of Lemma 3.6); reason: the proof uses c1 only through Lemma 3.6's conclusion
--   - reading: Algorithm 1 returns "any maximal D̂-bounded subgraph" → every fallback rule F; reason: the stronger reading
--   - generalization: n-node graphs with vertex set [n] → any common vertex set of n labels; reason: labels are identities; V = [n] is a special case
-- source:
--   Aden-Ali, Sealfon, Smith, Steinke, Ullman, Node Differential Privacy via Node-Stable Graph Projections, STOC 2027 submission (manuscript sha256 42f18565…), pp. 11–12, Lemma 3.3 item 3

import Mathlib
import Definitions.Def_NodeStableProj_Main_Stability
import Definitions.Def_NodeStableProj_Main_Projection

open MeasureTheory

namespace NodeStableProj.Main

/-- Lemma 3.3, item 3 (Stability), pp. 11–12: let `c1 > 0` be a constant for which Lemma 3.6
holds. For all `δ ∈ (0, 1)` and `n ∈ ℕ`, if `D̂ − D ≥ 2 c1 log(9n/δ)/ε̃` then `P_{D,D̂,ε̃}` is
`(ε, δ)`-distributionally node-stable on `n`-node graphs, where
`ε = ε̃ √(2 D̂ ln(3/δ)) + D̂ ε̃ (e^{ε̃} − 1)/(e^{ε̃} + 1)`, provided `ε ≤ 1`. -/
theorem lemma_3_3_stability (c1 : ℝ) (hc1 : 0 < c1) (hacc : SVTAccuracy c1)
    (D Dhat : ℕ) (εt : ℝ) (hD : 0 < D) (hDD : D < Dhat) (hεt : 0 < εt)
    (F : Graph → Graph) (hF : IsFallbackRule Dhat F)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (n : ℕ)
    (hgap : 2 * c1 * Real.log (9 * n / δ) / εt ≤ (Dhat : ℝ) - D)
    (hε : stabEps Dhat εt δ ≤ 1) :
    IsDistNodeStableOn n (alg1Law D Dhat εt F) (stabEps Dhat εt δ) δ := by sorry

end NodeStableProj.Main
