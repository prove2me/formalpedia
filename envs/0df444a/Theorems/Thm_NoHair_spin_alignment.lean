-- Prove2me | Theorems.Thm_NoHair_spin_alignment
-- name    : NoHair.spin_alignment
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-05T02:10:02.498363+00:00
-- url     : https://prove2.me/theorems/35f344f7-d0cc-40f7-a21a-657b3cfabf4a
-- title:
--   Changing the reference frame II: aligning the spin with the $z$-axis
-- statement:
--   For every vector $J=(J_0,J_1,J_2)\in\mathbb R^3$ there is a rotation $R\in SO(3)$ with
--   $$RJ=\big(0,0,\sqrt{J_0^2+J_1^2+J_2^2}\big).$$
--
--   This is the step of the source's frame argument that orients the spin angular momentum along the positive $z$-axis, leaving only its magnitude.
-- source:
--   Wikipedia, "No-hair theorem" (revision oldid=1353599195), https://en.wikipedia.org/w/index.php?title=No-hair_theorem&oldid=1353599195

import Mathlib
import Definitions.Def_NoHair_kerrNewman

open scoped ContDiff Manifold BigOperators
open Set Matrix

namespace NoHair

/-- **Milestone (changing the reference frame II): spin alignment.** Every angular-momentum
vector `J ∈ ℝ³` is rotated by some `R ∈ SO(3)` onto the positive `z`-axis: `R J = (0, 0, |J|)`. -/
theorem spin_alignment (J : Fin 3 → ℝ) :
    ∃ R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      R *ᵥ J = ![0, 0, Real.sqrt (J 0 ^ 2 + J 1 ^ 2 + J 2 ^ 2)] := by
  sorry

end NoHair
