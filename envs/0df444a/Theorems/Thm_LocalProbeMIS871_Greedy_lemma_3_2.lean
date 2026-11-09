-- Prove2me | Theorems.Thm_LocalProbeMIS871_Greedy_lemma_3_2
-- name    : LocalProbeMIS871.Greedy.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T01:53:00.113249+00:00
-- url     : https://prove2.me/theorems/dc48bab7-8509-4f9c-a9e6-b122d686dfbe
-- title:
--   Lemma 3.2 — An exponential-moment bound for M₅
-- statement:
--   Let $G$ be a finite simple undirected labeled graph, let $v$ be its fixed query root, and use the cached, early-stopping greedy evaluation. Write $R$ for its fresh evaluated vertices, $U=|R|$, $\tau(u)$ for elimination times, $M_s=\sum_{u\in R}\tau(u)^s$, $X=\sum_{u\in R\setminus\{v\}}\tau(u)^s$, $D=\sum_{u\in R\setminus\{v\}}\tau(u)^s\ln(r(u)/\tau(u))$, and $c_s=\ln(s-1)-1$. Unless stated otherwise below, the root has rank $1$ and the other ranks are independent uniforms on $(0,1)$.
--
--   With exactly $\kappa=1/160$,
--
--   $$\mathbb E\exp\left(\frac{M_5-1}{160}\right)\le2.$$
--
--   The subtraction is the printed constant one, even when the root is eliminated before time one.
--
--   Differences from the source:
--   - encoding: finite labeled graph and real rank assignment → Fin n, lexicographic real-rank/label keys, and computed cached execution; reason: zero-based labels enumerate exactly the same finite graphs and implement the source tie rule without adding a hypothesis
--   - encoding: probability and exponential expectation under the stated independent uniform ranks → the product rankLaw or its forced-root pushforward; exponential expectations use ExpBound; reason: the nonnegative Lebesgue integral and its measurability clause express the same random-variable expectation and cannot default to zero on divergence
-- source:
--   Peter Kiss, Yuichi Yoshida, The Local Probe Complexity of Maximal Independent Set, STOC 2027 submission #871 (October 2026), p. 12, PDF p. 14, Lemma 3.2, Eq.(7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/871.pdf

import Definitions.Def_LocalProbeMIS871_Greedy_Elimination

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false

namespace LocalProbeMIS871.Greedy

/-- Lemma 3.2, Eq.(7), printed p.12 / PDF14, κ exactly 1/160. -/
theorem lemma_3_2 {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    ExpBound (forcedLaw v) (fun r => (M G v 5 r - 1) / 160) 2 := by sorry

end LocalProbeMIS871.Greedy
