-- Prove2me | Theorems.Thm_O3_Experimental_hasDerivAt_scalarEnergy
-- name    : O3.Experimental.hasDerivAt_scalarEnergy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:54:29.78272+00:00
-- url     : https://prove2.me/theorems/4ddb66d3-73f8-4d3f-99ef-2535ae5d3028
-- title:
--   Experimental: has Deriv At scalar Energy
-- statement:
--   The Experimental construction uses the has Deriv At scalar Energy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/GeometryExperimental.lean#L135-L142
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/GeometryExperimental.lean#L135-L142

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_GeometryExperimental
set_option autoImplicit true
open O3 O3.Experimental

theorem O3.Experimental.hasDerivAt_scalarEnergy {p : ℝ} (hp : 2 < p) (x : ℝ) :
    HasDerivAt (scalarEnergy p) (scalarJ p x) x := by sorry
