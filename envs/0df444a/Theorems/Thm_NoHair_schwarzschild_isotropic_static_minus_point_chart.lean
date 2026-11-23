-- Prove2me | Theorems.Thm_NoHair_schwarzschild_isotropic_static_minus_point_chart
-- name    : NoHair.schwarzschild_isotropic_static_minus_point_chart
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T12:42:03.264866+00:00
-- url     : https://prove2.me/theorems/e119c51e-3f0e-49de-9694-4b287695a8b5
-- title:
--   Explicit smooth negative-sheet filling for every positive-mass Schwarzschild end
-- statement:
--   For static data agreeing near infinity with an isotropic Schwarzschild metric of mass m>0, unit inversion extends the negative conformal metric to the full ball as the constant matrix (m/2)⁴ times the identity.
-- source:
--   R. Beig and W. Simon, Proof of a multipole conjecture due to Geroch, Comm. Math. Phys. 78 (1980), 75–82, https://doi.org/10.1007/BF01941970. G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of multiple black holes in asymptotically Euclidean static vacuum space-time, Gen. Relativ. Gravit. 19 (1987), 147–154, https://doi.org/10.1007/BF00770326. These statements concern the lapse and its radial coordinate near the compactified end.

import Definitions.Def_NoHair_staticReflectionAndCap
import Definitions.Def_NoHair_staticInvertedEndMetric

open NoHair Set Filter Metric
open scoped Topology ContDiff

theorem NoHair.schwarzschild_isotropic_static_minus_point_chart (Ω : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) (R m : ℝ) (hR : 0 < R) (hm : 0 < m)
    (tail : ∀ x : ADMPoint, R<‖x‖ → x∈Ω ∧
      N x = (1-m/(2*‖x‖))/(1+m/(2*‖x‖)) ∧
      h x = (1+m/(2*‖x‖))^4 • (1:Matrix (Fin 3) (Fin 3) ℝ)) :
    ∃ a : StaticMinusPointChart Ω N h, a.radius = 1/R ∧
      (∀ y, a.change y = EuclideanGeometry.inversion (0:ADMPoint) 1 y) ∧
      ∀ y, a.coeff y = (m/2)^4 • (1:Matrix (Fin 3) (Fin 3) ℝ) := by
  sorry
