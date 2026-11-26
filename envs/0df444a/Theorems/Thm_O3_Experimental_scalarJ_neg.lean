-- Prove2me | Theorems.Thm_O3_Experimental_scalarJ_neg
-- name    : O3.Experimental.scalarJ_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:54:31.535673+00:00
-- url     : https://prove2.me/theorems/171a9a03-024f-40ff-9576-d20247832cf4
-- title:
--   Experimental: scalar J neg
-- statement:
--   The Experimental construction uses the scalar J neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/GeometryExperimental.lean#L204-L206
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/GeometryExperimental.lean#L204-L206

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_GeometryExperimental
set_option autoImplicit true
open O3 O3.Experimental

theorem O3.Experimental.scalarJ_neg (p x : ℝ) : scalarJ p (-x) = -scalarJ p x := by sorry
