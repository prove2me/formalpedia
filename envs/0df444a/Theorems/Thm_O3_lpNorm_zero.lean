-- Prove2me | Theorems.Thm_O3_lpNorm_zero
-- name    : O3.lpNorm_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:50:08.476126+00:00
-- url     : https://prove2.me/theorems/6c88ac63-5a40-45c9-a031-680ede085d9e
-- title:
--   O3: lp Norm zero
-- statement:
--   The O3 construction uses the lp Norm zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Geometry.lean#L50-L52
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Geometry.lean#L50-L52

import Mathlib
import Definitions.Def_O3_Geometry
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.lpNorm_zero {p : ℝ} (hp : 0 < p) {d : ℕ} :
    lpNorm p (0 : Point d) = 0 := by sorry
