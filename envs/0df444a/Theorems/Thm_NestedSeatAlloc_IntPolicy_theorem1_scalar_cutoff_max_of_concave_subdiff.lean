-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_scalar_cutoff_max_of_concave_subdiff
-- name    : NestedSeatAlloc.IntPolicy.theorem1_scalar_cutoff_max_of_concave_subdiff
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T11:39:18.330287+00:00
-- url     : https://prove2.me/theorems/982c550d-c7c8-499c-8d28-a3fa5aade075
-- title:
--   Scalar cutoff maximization from concavity and a fare subgradient
-- statement:
--   For a concave continuation value on nonnegative residual seats, if fare lies between its left and right one-sided derivatives at protection level p (with the usual boundary convention at p=0), then choosing p maximizes the scalar fare-plus-continuation payoff over every nonnegative alternative cutoff q and every fixed nonnegative demand x and seat level s.
-- source:
--   Source-faithful scalar core of the Brumelle-McGill dynamic-programming induction for theorem1_global_optimality_step_all_seats (d9b68cbf-156f-4fa7-a4ac-4abe5f223739). The proof derives monotonicity of g(t)-fare*t on either side of p from ConcaveOn and InSubdiff, then compares the residual seat count s-min(x,max(0,s-q)) in the three cases s≤p, p≤s≤p+x, and p+x≤s.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

theorem NestedSeatAlloc.IntPolicy.theorem1_scalar_cutoff_max_of_concave_subdiff
    (g : ℝ → ℝ) (fare p x s : ℝ) (hp : 0 ≤ p) (hx : 0 ≤ x) (hs : 0 ≤ s)
    (hconcave : ConcaveOn ℝ (Set.Ici 0) g) (hsubdiff : InSubdiff g p fare) :
    ∀ q, 0 ≤ q →
      fare * min x (max 0 (s - q)) + g (s - min x (max 0 (s - q))) ≤
        fare * min x (max 0 (s - p)) + g (s - min x (max 0 (s - p))) := by sorry
