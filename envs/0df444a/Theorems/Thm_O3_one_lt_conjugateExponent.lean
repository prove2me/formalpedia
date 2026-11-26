-- Prove2me | Theorems.Thm_O3_one_lt_conjugateExponent
-- name    : O3.one_lt_conjugateExponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:50:45.615125+00:00
-- url     : https://prove2.me/theorems/4fc1ceac-a8be-5e49-908e-6c53a765ee23
-- title:
--   O3: one lt conjugate Exponent
-- statement:
--   The O3 construction uses the one lt conjugate Exponent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Geometry.lean#L30-L32
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Geometry.lean#L30-L32

import Mathlib
import Definitions.Def_O3_Geometry
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.one_lt_conjugateExponent {p : ℝ} (hp : 1 < p) :
    1 < conjugateExponent p := by sorry
