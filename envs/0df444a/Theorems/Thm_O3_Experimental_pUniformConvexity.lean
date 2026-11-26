-- Prove2me | Theorems.Thm_O3_Experimental_pUniformConvexity
-- name    : O3.Experimental.pUniformConvexity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:55:04.977334+00:00
-- url     : https://prove2.me/theorems/5cfd5c88-455e-4989-833a-fd821601db23
-- title:
--   Experimental: p Uniform Convexity
-- statement:
--   The Experimental construction uses the p Uniform Convexity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/GeometryExperimental.lean#L229-L241
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/GeometryExperimental.lean#L229-L241

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_GeometryExperimental
set_option autoImplicit true
open O3 O3.Experimental

theorem O3.Experimental.pUniformConvexity {p : ℝ} (hp : 2 < p) {d : ℕ}
    (x y c : Point d) :
    uniformRegularizer p c y ≥
      uniformRegularizer p c x + pairing (powerDualityMap p (x - c)) (y - x) +
        (2 ^ (2 - p) / p) * (lpNorm p (y - x)) ^ p := by sorry
