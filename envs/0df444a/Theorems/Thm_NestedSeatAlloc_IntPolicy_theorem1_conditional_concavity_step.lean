-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_conditional_concavity_step
-- name    : NestedSeatAlloc.IntPolicy.theorem1_conditional_concavity_step
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-06T07:15:40.363979+00:00
-- url     : https://prove2.me/theorems/9f83cdf1-8bcd-4ba3-a686-fcbe52bed415
-- title:
--   Theorem 1 concavity step — extend conditional revenue by one fare class
-- statement:
--   For a protection policy satisfying the subdifferential condition at level k, concavity of the previous conditional revenue implies concavity of the next conditional revenue.
-- source:
--   Source-faithful one-step decomposition of Brumelle & McGill (1993), Theorem 1 concavity induction, pp. 131–132.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem theorem1_conditional_concavity_step {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (k : ℕ) (y : ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (hk : 1 ≤ k) (hy : 0 ≤ y)
    (h20k : InSubdiff (expRevenue P X f p k) (p k) (f (k + 1)))
    (hprev : ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p k y)) :
    ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p (k + 1) y) := by sorry

end NestedSeatAlloc.IntPolicy
