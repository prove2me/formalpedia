-- Prove2me | Theorems.Thm_O3_Experimental_scalarEnergy_neg
-- name    : O3.Experimental.scalarEnergy_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:54:26.11371+00:00
-- url     : https://prove2.me/theorems/27e27acc-b7ee-5912-a14b-57c0766a08ba
-- title:
--   Experimental: scalar Energy neg
-- statement:
--   The Experimental construction uses the scalar Energy neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/GeometryExperimental.lean#L208-L209
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/GeometryExperimental.lean#L208-L209

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_GeometryExperimental
set_option autoImplicit true
open O3 O3.Experimental

theorem O3.Experimental.scalarEnergy_neg (p x : ℝ) : scalarEnergy p (-x) = scalarEnergy p x := by sorry
