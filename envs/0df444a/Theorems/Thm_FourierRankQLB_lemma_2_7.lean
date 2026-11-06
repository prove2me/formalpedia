-- Prove2me | Theorems.Thm_FourierRankQLB_lemma_2_7
-- name    : FourierRankQLB.lemma_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:43:00.383026+00:00
-- url     : https://prove2.me/theorems/87960575-c5e3-47b6-bab1-18e79eeb7ef1
-- title:
--   Lemma 2.7 — approximately feasible output geometry
-- statement:
--   Let $K\subseteq\mathbb R^n$ be a convex body with $B_2(0,r)\subseteq K\subseteq B_2(0,R)$, let $0<\delta<r$, and let $c$ be a unit objective. If $y$ satisfies (8), that is $\operatorname{dist}(y,K)\le\delta$ and $c^Ty\ge h_{K^{-\delta}}(c)-\delta$, then there is $x\in K$ with $\|x-y\|\le\delta$ and
--   $$
--   c^Tx\ge h_K(c)-D,\qquad D=\delta\Bigl(\frac Rr+2\Bigr).
--   $$
--   Moreover
--   $$
--   h_K(c)-D\le c^Ty\le h_K(c)+\delta .
--   $$
--
--   The lemma converts the approximately feasible guarantee into a two-sided estimate of the true optimum.
--
--   Differences from the source:
--
--   - encoding: $K$ a convex body (compact, convex, nonempty interior) → `IsCompact K`, `Convex ℝ K`; reason: the nonempty interior follows from the inner ball, as $r>\delta>0$
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Lemma 2.7, p.15

import Mathlib
import Definitions.Def_FourierRankQLB_approxSuccess

namespace FourierRankQLB

/-- Lemma 2.7 (Approximately feasible output geometry). For a convex body with
`B₂(0, r) ⊆ K ⊆ B₂(0, R)` and `0 < δ < r`, a point `y` satisfying (8) for a unit objective `c` has a
point `x ∈ K` with `‖x - y‖ ≤ δ` and `cᵀx ≥ h_K(c) - D`, `D = δ(R/r + 2)` (9), and
`h_K(c) - D ≤ cᵀy ≤ h_K(c) + δ` (10).

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Lemma 2.7, p. 15.

**Formalization Note.** `K` is compact and convex, the paper's standing "convex body" of p. 13. Its
nonempty interior follows from the inner ball, as `0 < δ < r`. -/
theorem lemma_2_7 {n : ℕ} {K : Set (Ambient n)} (hKc : IsCompact K) (hKconv : Convex ℝ K)
    {r R δ : ℝ} (hr : Metric.closedBall (0 : Ambient n) r ⊆ K)
    (hR : K ⊆ Metric.closedBall (0 : Ambient n) R) (hδ : 0 < δ) (hδr : δ < r)
    {c y : Ambient n} (hc : ‖c‖ = 1) (hy : y ∈ approxSuccess K c δ) :
    (∃ x ∈ K, ‖x - y‖ ≤ δ ∧ supportFn K c - δ * (R / r + 2) ≤ inner ℝ c x) ∧
      supportFn K c - δ * (R / r + 2) ≤ inner ℝ c y ∧
      inner ℝ c y ≤ supportFn K c + δ := by sorry

end FourierRankQLB
