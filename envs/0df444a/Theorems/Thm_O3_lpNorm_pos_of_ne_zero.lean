-- Prove2me | Theorems.Thm_O3_lpNorm_pos_of_ne_zero
-- name    : O3.lpNorm_pos_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:50:53.586722+00:00
-- url     : https://prove2.me/theorems/27ba4727-5637-4dfd-9d11-441b0e84687b
-- title:
--   O3: lp Norm pos of ne zero
-- statement:
--   The O3 construction uses the lp Norm pos of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Geometry.lean#L68-L70
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Geometry.lean#L68-L70

import Mathlib
import Definitions.Def_O3_Geometry
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.lpNorm_pos_of_ne_zero {p : ℝ} {d : ℕ} {x : Point d}
    (hx : x ≠ 0) : 0 < lpNorm p x := by sorry
