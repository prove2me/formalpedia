-- Prove2me | Theorems.Thm_O3_Experimental_scalarUniformConvexity
-- name    : O3.Experimental.scalarUniformConvexity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:54:45.571223+00:00
-- url     : https://prove2.me/theorems/2bcd9c4c-d71d-5c54-9d93-97bd3389ab80
-- title:
--   Experimental: scalar Uniform Convexity
-- statement:
--   The Experimental construction uses the scalar Uniform Convexity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/GeometryExperimental.lean#L211-L221
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/GeometryExperimental.lean#L211-L221

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_GeometryExperimental
set_option autoImplicit true
open O3 O3.Experimental

theorem O3.Experimental.scalarUniformConvexity {p x y : ℝ} (hp : 2 < p) :
    scalarEnergy p y ≥ scalarEnergy p x + scalarJ p x * (y - x) +
      ((2 : ℝ) ^ (2 - p) / p) * |y - x| ^ p := by sorry
