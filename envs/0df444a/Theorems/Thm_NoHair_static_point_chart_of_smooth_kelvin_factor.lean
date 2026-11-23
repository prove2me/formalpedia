-- Prove2me | Theorems.Thm_NoHair_static_point_chart_of_smooth_kelvin_factor
-- name    : NoHair.static_point_chart_of_smooth_kelvin_factor
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T12:40:12.939501+00:00
-- url     : https://prove2.me/theorems/c28de7ff-2e7d-47ce-af8e-891cbe8d3f1a
-- title:
--   Smooth static point filling from a regular Kelvin factor
-- statement:
--   If the negative conformal metric is Euclidean up to a scalar and its Kelvin-transformed conformal factor extends smoothly and positively on a ball, unit inversion gives a smooth positive metric across the added point with coefficients f⁴δ.
-- source:
--   R. Beig and W. Simon, Proof of a multipole conjecture due to Geroch, Comm. Math. Phys. 78 (1980), 75–82, https://doi.org/10.1007/BF01941970. G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of multiple black holes in asymptotically Euclidean static vacuum space-time, Gen. Relativ. Gravit. 19 (1987), 147–154, https://doi.org/10.1007/BF00770326. These statements concern the lapse and its radial coordinate near the compactified end.

import Definitions.Def_NoHair_staticReflectionAndCap
import Definitions.Def_NoHair_staticInvertedEndMetric

open NoHair Set Filter Metric
open scoped Topology ContDiff

theorem NoHair.static_point_chart_of_smooth_kelvin_factor (Ω : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) (R : ℝ) (hR : 0<R)
    (f : ADMPoint → ℝ) (sf : ContDiffOn ℝ ∞ f (ball 0 (1/R)))
    (pf : ∀ y ∈ ball (0:ADMPoint) (1/R), 0<f y)
    (inside : ∀ x : ADMPoint, R<‖x‖ → x∈Ω)
    (tail : ∀ x : ADMPoint, R<‖x‖ → staticPositiveMetric (fun z => -N z) h x =
      (f (EuclideanGeometry.inversion (0:ADMPoint) 1 x)/‖x‖)^4 • (1:Matrix (Fin 3) (Fin 3) ℝ)) :
    ∃ a : StaticMinusPointChart Ω N h, a.radius = 1/R ∧
      (∀ y, a.change y = EuclideanGeometry.inversion (0:ADMPoint) 1 y) ∧
      ∀ y, a.coeff y = (f y)^4 • (1:Matrix (Fin 3) (Fin 3) ℝ) := by
  sorry
