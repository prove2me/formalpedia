-- Prove2me | Theorems.Thm_JHolomorphic_eLpNorm_restrict_le_of_subset_biUnion
-- name    : JHolomorphic.eLpNorm_restrict_le_of_subset_biUnion
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T23:53:30.671031+00:00
-- url     : https://prove2.me/theorems/978017b2-e921-4865-8c10-343ec5b866a1
-- title:
--   $L^q$ norms on a set covered by finitely many discs
-- statement:
--   Let $F$ be a normed space, $f:\mathbb C\to F$ strongly measurable, $1\le q\le\infty$, $K\subseteq\mathbb C$ measurable, $t\subseteq\mathbb C$ a finite set and $r\in\mathbb R$ with $K\subseteq\bigcup_{x\in t}B(x,r)$. If $\|f\|_{L^q(B(x,r))}\le C$ for every $x\in t$, then
--   $$\|f\|_{L^q(K)}\le \#t\cdot C.$$
--   This turns uniform local $L^q$ bounds on discs into bounds on compact sets.
--
--   **Formalization Note** `f` is `AEStronglyMeasurable` for `volume`; the norms are `eLpNorm f q (volume.restrict ·)` with `q : ℝ≥0∞`, `1 ≤ q`, and `C : ℝ≥0∞`; `t : Finset ℂ`.
-- source:
--   Elementary measure theory; used for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Theorem 2.22

import Definitions.Def_JHolomorphic_Setting
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

namespace JHolomorphic

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal

/-- If a measurable set `K ⊆ ℂ` is covered by the discs `B(x, r)`, `x ∈ t`, for a finite set
`t`, and `‖f‖_{L^q(B(x,r))} ≤ C` for every `x ∈ t` (`q ≥ 1`), then `‖f‖_{L^q(K)} ≤ #t · C`. -/
theorem eLpNorm_restrict_le_of_subset_biUnion {F : Type*} [NormedAddCommGroup F]
    {f : ℂ → F} (hf : AEStronglyMeasurable f volume) {q : ℝ≥0∞} (hq : 1 ≤ q) (K : Set ℂ)
    (hKm : MeasurableSet K) (t : Finset ℂ) (r : ℝ) (hK : K ⊆ ⋃ x ∈ t, ball x r) (C : ℝ≥0∞)
    (h : ∀ x ∈ t, eLpNorm f q (volume.restrict (ball x r)) ≤ C) :
    eLpNorm f q (volume.restrict K) ≤ t.card * C := by
  sorry

end JHolomorphic
