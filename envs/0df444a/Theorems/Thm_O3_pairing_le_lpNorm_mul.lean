-- Prove2me | Theorems.Thm_O3_pairing_le_lpNorm_mul
-- name    : O3.pairing_le_lpNorm_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:50:38.571012+00:00
-- url     : https://prove2.me/theorems/841e765e-151f-5847-a0e1-8d870b5e8212
-- title:
--   O3: pairing le lp Norm mul
-- statement:
--   Finite-dimensional Hölder inequality in the exact explicit norms used by O3.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Geometry.lean#L101-L105
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Geometry.lean#L101-L105

import Mathlib
import Definitions.Def_O3_Geometry
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.pairing_le_lpNorm_mul {p q : ℝ} (hpq : p.HolderConjugate q)
    {d : ℕ} (x y : Point d) :
    pairing x y ≤ lpNorm p x * lpNorm q y := by sorry
