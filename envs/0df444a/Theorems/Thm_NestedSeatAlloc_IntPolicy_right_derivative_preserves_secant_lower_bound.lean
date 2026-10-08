-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_right_derivative_preserves_secant_lower_bound
-- name    : NestedSeatAlloc.IntPolicy.right_derivative_preserves_secant_lower_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T22:41:18.260004+00:00
-- url     : https://prove2.me/theorems/1f435294-350f-4348-bfad-72b5d3578082
-- title:
--   A right-derivative limit preserves a closed lower bound on secants
-- statement:
--   If every strictly rightward secant slope of a real function from a point is at least c, then any right derivative at that point is also at least c.
-- source:
--   Source-faithful closed-limit calculus lemma used in the base-fare argument for theorem1_global_optimality_step_all_seats (d9b68cbf-156f-4fa7-a4ac-4abe5f223739). The source proof converts HasDerivWithinAt on Ici a to convergence of the slope map on the punctured right filter, transfers membership in the closed interval Ici c through the limit, and concludes c ≤ r.

import Mathlib

open Filter
open scoped Topology

namespace NestedSeatAlloc.IntPolicy

theorem right_derivative_preserves_secant_lower_bound
    (g : ℝ → ℝ) (a r c : ℝ)
    (hderiv : HasDerivWithinAt g r (Set.Ici a) a)
    (hsec : ∀ y, a < y → c ≤ slope g a y) :
    c ≤ r := by sorry

end NestedSeatAlloc.IntPolicy
