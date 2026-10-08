-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_all_seat_optimum_implies_intermediate_subdiff
-- name    : NestedSeatAlloc.IntPolicy.theorem1_all_seat_optimum_implies_intermediate_subdiff
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T21:22:20.611983+00:00
-- url     : https://prove2.me/theorems/304a5ba4-c3fe-4878-9ae0-c209084c89c1
-- title:
--   Theorem 1 bridge: all-seat prefix optimality yields intermediate subdifferentials
-- statement:
--   Under the nested seat model, if p maximizes level-k expected revenue over every protection policy at every nonnegative seat count, then every transition j→j+1 with positive probability of nonzero next-class demand satisfies the one-sided subdifferential condition for the level-j expected revenue at p_j. The derivative weights are the probabilities that the upper residual-seat path enters the cutoff interval; varying the outer seat count guarantees a positive strict-interior weight for some rational seat. If the next demand is zero almost surely, the recursion instead collapses and no derivative condition is needed.
-- source:
--   Source-faithful consequence of the exact three-branch recursion (Definitions.Def_NestedSeatAlloc_IntPolicy_Model) and hprev in theorem1_global_optimality_step_all_seats (d9b68cbf-156f-4fa7-a4ac-4abe5f223739), obtained by varying only q_j and composing residual maps rho_m(v,x,a)=min(v,max(a,v-x)) for m=j+2,...,k. The derivation records the distinct endpoint events for right and left derivatives and the rational-seat positive-weight argument.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

theorem NestedSeatAlloc.IntPolicy.theorem1_all_seat_optimum_implies_intermediate_subdiff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (k : ℕ) (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p) (hk : 1 ≤ k) (hprev : ∀ t, 0 ≤ t → ∀ q, IsProtectionPolicy q → expRevenue P X f q k t ≤ expRevenue P X f p k t) : ∀ j, 1 ≤ j → j < k → 0 < P.real {ω | 0 < X (j + 1) ω} → InSubdiff (expRevenue P X f p j) (p j) (f (j + 1)) := by sorry
