-- Prove2me | Theorems.Thm_O3_Stage2RouteC_ballCarlenLieb_fin_one
-- name    : O3.Stage2RouteC.ballCarlenLieb_fin_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:06:16.321306+00:00
-- url     : https://prove2.me/theorems/c5f6ccd9-744f-534e-91c0-2953bf6157a2
-- title:
--   Stage2 Route C: ball Carlen Lieb fin one
-- statement:
--   One-dimensional sanity check for the whole real range `1 < p ≤ 2`.
--   The exact coefficient follows from a scalar square identity.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteC.lean#L83-L90
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteC.lean#L83-L90

import Definitions.Def_O3_Geometry
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Definitions.Def_O3_Stage2RouteC
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteC

theorem O3.Stage2RouteC.ballCarlenLieb_fin_one {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (u v : O3.Point 1) :
    (O3.lpNorm p (u + v)) ^ (2 : ℕ) +
        (p - 1) * (O3.lpNorm p (u - v)) ^ (2 : ℕ) ≤
      2 * ((O3.lpNorm p u) ^ (2 : ℕ) + (O3.lpNorm p v) ^ (2 : ℕ)) := by sorry
