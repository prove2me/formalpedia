-- Prove2me | Theorems.Thm_Gerver_rotation_angle_right
-- name    : Gerver.rotation_angle_right
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-19T20:13:02.944129+00:00
-- url     : https://prove2.me/theorems/ae8385a6-479e-430b-b558-224721cf2a15
-- title:
--   A balanced maximum sofa of large area can be turned through the full right angle
-- statement:
--   A balanced maximum sofa of area at least 2.2 whose rotation angle lies between arccos(1/2.2) and π/2 has a rotated copy that admits a movement of rotation angle π/2. This is the reduction that confines the endgame to sofas moving through the full right angle: since the sofa area is known to be at least 2.2195... by Gerver's construction, any balanced maximum sofa of large area can be rigidly rotated so that its supporting movement turns the full π/2.
-- source:
--   Baek (2024), Optimality of Gerver's Sofa, arXiv:2411.19826, Theorem 1.5.2 (Step 1-(c) of the proof outline)

import Mathlib
import Definitions.Def_Gerver_arena
import Definitions.Def_Gerver_monotone
import Definitions.Def_Gerver_sofa

namespace Gerver

/-- Step 1c (Theorem 1.5.2): a balanced maximum sofa of area at least 2.2 and
rotation angle in [sec⁻¹(2.2), π/2] has a rotated copy that admits a movement
of rotation angle π/2. -/
theorem rotation_angle_right (S : Set (ℝ × ℝ)) {ω : ℝ}
    (hbal : IsBalancedMaximumSofa S ω) (hmov : HasMovementAngle S ω)
    (ha : 2.2 ≤ area S)
    (hω : Real.arccos (1 / 2.2) ≤ ω ∧ ω ≤ Real.pi / 2) :
    ∃ δ, HasMovementAngle ((fun p => rot δ p) '' S) (Real.pi / 2) := by
  sorry

end Gerver
