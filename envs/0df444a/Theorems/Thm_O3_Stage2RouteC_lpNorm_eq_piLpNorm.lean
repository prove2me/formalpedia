-- Prove2me | Theorems.Thm_O3_Stage2RouteC_lpNorm_eq_piLpNorm
-- name    : O3.Stage2RouteC.lpNorm_eq_piLpNorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:04:50.56027+00:00
-- url     : https://prove2.me/theorems/61421608-f4b7-5133-b827-77e3ff91d46a
-- title:
--   Stage2 Route C: lp Norm eq pi Lp Norm
-- statement:
--   The literal O3 norm is definitionally the finite `PiLp` norm after the
--   standard `ENNReal.ofReal` exponent conversion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteC.lean#L22-L29
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteC.lean#L22-L29

import Definitions.Def_O3_Geometry
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Definitions.Def_O3_Stage2RouteC
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteC

theorem O3.Stage2RouteC.lpNorm_eq_piLpNorm {p : ℝ} (hp : 1 ≤ p) {d : ℕ} (x : O3.Point d) :
    O3.lpNorm p x =
      ‖(WithLp.toLp (ENNReal.ofReal p) x :
        PiLp (ENNReal.ofReal p) (fun _ : Fin d ↦ ℝ))‖ := by sorry
