-- Prove2me | Theorems.Thm_Gerver_rotation_angle_range
-- name    : Gerver.rotation_angle_range
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-19T20:11:45.169635+00:00
-- url     : https://prove2.me/theorems/4dd3ea38-8e8a-488a-87ae-7e0e667b5ed3
-- title:
--   Big sofas turn most of the right angle
-- statement:
--   Every moving sofa of area at least 2.2 admits a movement whose rotation angle — the total clockwise turn of the movement — lies between sec⁻¹(2.2) and π/2. This is Gerver's bound: a sofa too large to fit in the intersection of two strips at a shallow angle must rotate through nearly the full right angle. Combined with Gerver's sofa of area 2.2195..., it restricts the rotation angle of a maximum-area sofa to [sec⁻¹(2.2), π/2].
-- source:
--   Baek (2024), Optimality of Gerver's Sofa, arXiv:2411.19826, Theorem 1.5.1 (modification of page 271 of Gerver 1992)

import Mathlib
import Definitions.Def_Gerver_arena
import Definitions.Def_Gerver_monotone
import Definitions.Def_Gerver_sofa

namespace Gerver

/-- Step 1c (Theorem 1.5.1, Gerver): a moving sofa of area at least 2.2 admits
a movement whose rotation angle lies between sec⁻¹(2.2) and π/2. -/
theorem rotation_angle_range (S : Set (ℝ × ℝ)) (hS : IsMovingSofa S)
    (ha : 2.2 ≤ area S) :
    ∃ ω, HasMovementAngle S ω ∧ Real.arccos (1 / 2.2) ≤ ω ∧ ω ≤ Real.pi / 2 := by
  sorry

end Gerver
