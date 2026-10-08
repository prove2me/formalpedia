-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_d9_scalar_cutoff_max_of_concave_subdiff
-- name    : NestedSeatAlloc.IntPolicy.d9_scalar_cutoff_max_of_concave_subdiff
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T01:36:18.336778+00:00
-- url     : https://prove2.me/theorems/85c1bbfd-5b9a-4c0f-806f-38b7a4fe9aa5
-- title:
--   Scalar cutoff maximization from concavity and a subdifferential
-- statement:
--   For a concave prefix revenue function, if the next fare lies in its one-sided subdifferential at the protection threshold p, then choosing p maximizes the one-step scalar revenue over every nonnegative competing cutoff q, for any nonnegative demand and seat count.
-- source:
--   Source-faithful scalar reduction of the exact three-branch recurrence in Definitions.Def_NestedSeatAlloc_IntPolicy_Model, used by theorem1_global_optimality_step_all_seats (d9b68cbf-156f-4fa7-a4ac-4abe5f223739). The clipped next-class allocation is min x (max 0 (s-q)); after rewriting the payoff as fare*s + (g(residual)-fare*residual), concavity and InSubdiff make the tilted prefix value increase up to p and decrease after p. This isolates the scalar cutoff step and does not claim the parent concavity or expectation-factorization obligations are solved.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

theorem NestedSeatAlloc.IntPolicy.d9_scalar_cutoff_max_of_concave_subdiff (g : ℝ → ℝ) (fare p x s : ℝ) (hp : 0 ≤ p) (hx : 0 ≤ x) (hs : 0 ≤ s) (hconcave : ConcaveOn ℝ (Set.Ici 0) g) (hsubdiff : InSubdiff g p fare) : ∀ q, 0 ≤ q → fare * min x (max 0 (s - q)) + g (s - min x (max 0 (s - q))) ≤ fare * min x (max 0 (s - p)) + g (s - min x (max 0 (s - p))) := by sorry
