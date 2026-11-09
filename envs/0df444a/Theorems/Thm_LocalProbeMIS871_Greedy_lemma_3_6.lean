-- Prove2me | Theorems.Thm_LocalProbeMIS871_Greedy_lemma_3_6
-- name    : LocalProbeMIS871.Greedy.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T01:53:49.289969+00:00
-- url     : https://prove2.me/theorems/5b7c209a-492c-4605-940e-cb5685dfa802
-- title:
--   Lemma 3.6 — An exponential-moment bound using M₁
-- statement:
--   Let $G$ be a finite simple undirected labeled graph, let $v$ be its fixed query root, and use the cached, early-stopping greedy evaluation. Write $R$ for its fresh evaluated vertices, $U=|R|$, $\tau(u)$ for elimination times, $M_s=\sum_{u\in R}\tau(u)^s$, $X=\sum_{u\in R\setminus\{v\}}\tau(u)^s$, $D=\sum_{u\in R\setminus\{v\}}\tau(u)^s\ln(r(u)/\tau(u))$, and $c_s=\ln(s-1)-1$. Unless stated otherwise below, the root has rank $1$ and the other ranks are independent uniforms on $(0,1)$.
--
--   If $\Delta\ge2$ is an integer bounding every degree, then
--
--   $$\mathbb E\exp\left(\frac{U-2}{2}-2\Delta M_1\right)\le1.$$
--
--   This bounds the total fresh evaluations relative to their first elimination-time moment.
--
--   Differences from the source:
--   - encoding: finite labeled graph and real rank assignment → Fin n, lexicographic real-rank/label keys, and computed cached execution; reason: zero-based labels enumerate exactly the same finite graphs and implement the source tie rule without adding a hypothesis
--   - encoding: probability and exponential expectation under the stated independent uniform ranks → the product rankLaw or its forced-root pushforward; exponential expectations use ExpBound; reason: the nonnegative Lebesgue integral and its measurability clause express the same random-variable expectation and cannot default to zero on divergence
-- source:
--   Peter Kiss, Yuichi Yoshida, The Local Probe Complexity of Maximal Independent Set, STOC 2027 submission #871 (October 2026), p. 14, PDF p. 16, Lemma 3.6, Eq.(12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/871.pdf

import Definitions.Def_LocalProbeMIS871_Greedy_Elimination

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false

namespace LocalProbeMIS871.Greedy

/-- Lemma 3.6, Eq.(12), printed p.14 / PDF16. -/
theorem lemma_3_6 {n : ℕ} (G : SimpleGraph (Fin n)) (Δ : ℕ) (hΔ : 2 ≤ Δ)
    (hdeg : ∀ u, G.degree u ≤ Δ) (v : Fin n) :
    ExpBound (forcedLaw v) (fun r => ((U G v r : ℝ) - 2) / 2 - 2 * Δ * M G v 1 r) 1 := by sorry

end LocalProbeMIS871.Greedy
