-- Prove2me | Theorems.Thm_O3_abs_pairing_le_lpNorm_mul
-- name    : O3.abs_pairing_le_lpNorm_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:51:02.530534+00:00
-- url     : https://prove2.me/theorems/355737ac-dd49-5a5b-88f5-6849c1be5d61
-- title:
--   O3: abs pairing le lp Norm mul
-- statement:
--   Absolute-value form of finite-dimensional Hölder.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Geometry.lean#L108-L119
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Geometry.lean#L108-L119

import Mathlib
import Definitions.Def_O3_Geometry
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.abs_pairing_le_lpNorm_mul {p q : ℝ} (hpq : p.HolderConjugate q)
    {d : ℕ} (x y : Point d) :
    |pairing x y| ≤ lpNorm p x * lpNorm q y := by sorry
