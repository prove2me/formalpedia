-- Prove2me | Theorems.Thm_O3_lpNorm_neg
-- name    : O3.lpNorm_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:50:14.374186+00:00
-- url     : https://prove2.me/theorems/a142537c-e71d-473a-bed1-80113b5d0437
-- title:
--   O3: lp Norm neg
-- statement:
--   The O3 construction uses the lp Norm neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Geometry.lean#L85-L87
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Geometry.lean#L85-L87

import Mathlib
import Definitions.Def_O3_Geometry
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.lpNorm_neg (p : ℝ) {d : ℕ} (x : Point d) :
    lpNorm p (-x) = lpNorm p x := by sorry
