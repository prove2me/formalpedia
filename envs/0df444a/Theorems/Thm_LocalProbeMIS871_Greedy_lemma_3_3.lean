-- Prove2me | Theorems.Thm_LocalProbeMIS871_Greedy_lemma_3_3
-- name    : LocalProbeMIS871.Greedy.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T01:53:13.758893+00:00
-- url     : https://prove2.me/theorems/7d594652-ab96-4178-9d34-b8b60823b8c4
-- title:
--   Lemma 3.3 — From Mₛ to the number of evaluated vertices
-- statement:
--   Let $G$ be a finite simple undirected labeled graph, let $v$ be its fixed query root, and use the cached, early-stopping greedy evaluation. Write $R$ for its fresh evaluated vertices, $U=|R|$, $\tau(u)$ for elimination times, $M_s=\sum_{u\in R}\tau(u)^s$, $X=\sum_{u\in R\setminus\{v\}}\tau(u)^s$, $D=\sum_{u\in R\setminus\{v\}}\tau(u)^s\ln(r(u)/\tau(u))$, and $c_s=\ln(s-1)-1$. Unless stated otherwise below, the root has rank $1$ and the other ranks are independent uniforms on $(0,1)$.
--
--   If the integer $\Delta\ge2$ bounds every degree, then for every real $s>1$,
--
--   $$\mathbb E\exp\left(\frac{U-(8\Delta)^sM_s}{4}\right)\le e.$$
--
--   This retains the full real-exponent comparison between fresh evaluations and elimination moments.
--
--   Differences from the source:
--   - encoding: finite labeled graph and real rank assignment → Fin n, lexicographic real-rank/label keys, and computed cached execution; reason: zero-based labels enumerate exactly the same finite graphs and implement the source tie rule without adding a hypothesis
--   - encoding: probability and exponential expectation under the stated independent uniform ranks → the product rankLaw or its forced-root pushforward; exponential expectations use ExpBound; reason: the nonnegative Lebesgue integral and its measurability clause express the same random-variable expectation and cannot default to zero on divergence
-- source:
--   Peter Kiss, Yuichi Yoshida, The Local Probe Complexity of Maximal Independent Set, STOC 2027 submission #871 (October 2026), p. 12, PDF p. 14, Lemma 3.3, Eq.(8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/871.pdf

import Definitions.Def_LocalProbeMIS871_Greedy_Elimination

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false

namespace LocalProbeMIS871.Greedy

/-- Lemma 3.3, Eq.(8), printed p.12 / PDF14; arbitrary real s>1. -/
theorem lemma_3_3 {n : ℕ} (G : SimpleGraph (Fin n)) (Δ : ℕ) (hΔ : 2 ≤ Δ)
    (hdeg : ∀ u, G.degree u ≤ Δ) (v : Fin n) (s : ℝ) (hs : 1 < s) :
    ExpBound (forcedLaw v)
      (fun r => ((U G v r : ℝ) - (8 * (Δ : ℝ)) ^ s * M G v s r) / 4) (Real.exp 1) := by sorry

end LocalProbeMIS871.Greedy
