-- Prove2me | Theorems.Thm_Gerver_balanced_maximum_exists
-- name    : Gerver.balanced_maximum_exists
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-19T20:12:33.366113+00:00
-- url     : https://prove2.me/theorems/8e8e42ce-1a81-4f28-8aa6-3f79a8225214
-- title:
--   Balanced maximum sofas exist for each rotation angle
-- statement:
--   For every rotation angle ω ∈ (0, π/2] there exists a moving sofa S that is a balanced maximum sofa of angle ω — the Hausdorff limit of maximum polygon sofas whose uniform angle sets Θ_{ω,n_i} run over a strictly increasing sequence of powers of two — such that S admits a movement of rotation angle ω and the area of S equals the maximum area m_ω of a moving sofa admitting such a movement. This is the limit construction that turns Gerver's balancing argument into an actual maximizer: maximum polygon sofas are balanced, and their limit is a genuine moving sofa attaining the supremum.
-- source:
--   Baek (2024), Optimality of Gerver's Sofa, arXiv:2411.19826, Theorem 3.5.2 and Theorem 3.5.6 (Step 1-(b) of the proof outline)

import Mathlib
import Definitions.Def_Gerver_arena
import Definitions.Def_Gerver_monotone
import Definitions.Def_Gerver_sofa

namespace Gerver

/-- Step 1b (Theorem 3.5.2 and Theorem 3.5.6): for every rotation angle
ω ∈ (0, π/2] there is a balanced maximum sofa of rotation angle ω, and it
attains the maximum area among all moving sofas admitting a movement of
rotation angle ω. -/
theorem balanced_maximum_exists (ω : ℝ) (hω : 0 < ω) (hω' : ω ≤ Real.pi / 2) :
    ∃ S, IsBalancedMaximumSofa S ω ∧ HasMovementAngle S ω ∧ area S = angleMax ω := by
  sorry

end Gerver
