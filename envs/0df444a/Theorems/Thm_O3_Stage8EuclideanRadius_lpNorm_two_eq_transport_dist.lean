-- Prove2me | Theorems.Thm_O3_Stage8EuclideanRadius_lpNorm_two_eq_transport_dist
-- name    : O3.Stage8EuclideanRadius.lpNorm_two_eq_transport_dist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:17:49.466196+00:00
-- url     : https://prove2.me/theorems/bb37be60-aa9e-4e2e-8e53-cfe170a143e0
-- title:
--   Stage8 Euclidean Radius: lp Norm two eq transport dist
-- statement:
--   The literal `lpNorm 2` is exactly distance after transport to `PiLp 2`.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage8EuclideanRadius.lean#L33-L43
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage8EuclideanRadius.lean#L33-L43

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_O3_Stage8EuclideanRadius
set_option autoImplicit true
open O3 O3.Stage8EuclideanRadius
open O3

theorem O3.Stage8EuclideanRadius.lpNorm_two_eq_transport_dist {d : ℕ} (x y : Vec d) :
    lpNorm 2 (x - y) =
      dist
        (WithLp.toLp (ENNReal.ofReal (2 : ℝ)) x : EuclideanLpSpace d)
        (WithLp.toLp (ENNReal.ofReal (2 : ℝ)) y : EuclideanLpSpace d) := by sorry
