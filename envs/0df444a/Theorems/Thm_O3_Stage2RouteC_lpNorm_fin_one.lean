-- Prove2me | Theorems.Thm_O3_Stage2RouteC_lpNorm_fin_one
-- name    : O3.Stage2RouteC.lpNorm_fin_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:04:55.153968+00:00
-- url     : https://prove2.me/theorems/0994f943-581c-509d-937a-2bae9a68ae61
-- title:
--   Stage2 Route C: lp Norm fin one
-- statement:
--   In one dimension the literal `ell_p` norm is absolute value for every
--   positive real exponent.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteC.lean#L74-L79
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteC.lean#L74-L79

import Definitions.Def_O3_Geometry
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Definitions.Def_O3_Stage2RouteC
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteC

theorem O3.Stage2RouteC.lpNorm_fin_one {p : ℝ} (hp : 0 < p) (x : O3.Point 1) :
    O3.lpNorm p x = |x 0| := by sorry
