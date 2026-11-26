-- Prove2me | Theorems.Thm_O3_Experimental_scalarUniformConvexity_of_le
-- name    : O3.Experimental.scalarUniformConvexity_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:54:15.209474+00:00
-- url     : https://prove2.me/theorems/7099c4f1-08e0-5213-b3cb-ab40c8d8440c
-- title:
--   Experimental: scalar Uniform Convexity of le
-- statement:
--   The Experimental construction uses the scalar Uniform Convexity of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/GeometryExperimental.lean#L148-L202
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/GeometryExperimental.lean#L148-L202

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_GeometryExperimental
set_option autoImplicit true
open O3 O3.Experimental

theorem O3.Experimental.scalarUniformConvexity_of_le {p x y : ℝ} (hp : 2 < p) (hxy : x ≤ y) :
    scalarEnergy p y ≥ scalarEnergy p x + scalarJ p x * (y - x) +
      ((2 : ℝ) ^ (2 - p) / p) * |y - x| ^ p := by sorry
