-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_global_optimality_step_all_seats
-- name    : NestedSeatAlloc.IntPolicy.theorem1_global_optimality_step_all_seats
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:49:33.000931+00:00
-- url     : https://prove2.me/theorems/d9b68cbf-156f-4fa7-a4ac-4abe5f223739
-- title:
--   Theorem 1 optimality step with all-seat prefix dominance
-- statement:
--   If a policy p satisfies the subdifferential condition at level k and dominates every protection policy for the k-class expected revenue at every nonnegative seat count, then p also dominates every protection policy for the (k+1)-class expected revenue at every nonnegative seat count.
-- source:
--   Brumelle & McGill (1993), proof of Theorem 1, pp. 131-132: dynamic-programming induction, with the prefix dominance hypothesis applied at every residual seat level and condition (20) supplying the supporting-line inequality at p_k.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem theorem1_global_optimality_step_all_seats {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (k : ℕ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p) (hk : 1 ≤ k)
    (h20k : InSubdiff (expRevenue P X f p k) (p k) (f (k + 1)))
    (hprev : ∀ t, 0 ≤ t → ∀ q, IsProtectionPolicy q →
      expRevenue P X f q k t ≤ expRevenue P X f p k t) :
    ∀ s, 0 ≤ s → ∀ q, IsProtectionPolicy q →
      expRevenue P X f q (k + 1) s ≤ expRevenue P X f p (k + 1) s := by sorry

end NestedSeatAlloc.IntPolicy
