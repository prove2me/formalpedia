-- Prove2me | Theorems.Thm_O3_Stage2RouteB_conjugateExponent_sub_one
-- name    : O3.Stage2RouteB.conjugateExponent_sub_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:20:30.359288+00:00
-- url     : https://prove2.me/theorems/db63dec5-212e-4010-b6f0-e6aa1d4ae0ea
-- title:
--   Stage2 Route B: conjugate Exponent sub one
-- statement:
--   The Stage2 Route B construction uses the conjugate Exponent sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteB.lean#L260-L265
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteB.lean#L260-L265

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteB

theorem O3.Stage2RouteB.conjugateExponent_sub_one {p : ℝ} (hp : 1 < p) :
    conjugateExponent p - 1 = 1 / (p - 1) := by sorry
