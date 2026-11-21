-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_first_safe_axis_tangent_le
-- name    : NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_first_safe_axis_tangent_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T04:00:47.734689+00:00
-- url     : https://prove2.me/theorems/79c7a623-5ed5-4402-af81-2476281dd592
-- title:
--   Newtonian Point Source: acceleration Field fderiv first safe axis tangent le
-- statement:
--   The true Newtonian Frechet derivative has 5/4
--   tangential directional factor under arbitrary signs and
--   positive Cartesian clearance on the first coordinate.
--   The physical Euclidean denominator is unchanged.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/PhysicalTangentialFirstAxis.lean#L104-L125
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/PhysicalTangentialFirstAxis.lean#L104-L125

module
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialNormalized
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialFirstAxis
set_option autoImplicit true
@[expose] public section
public section
open Matrix
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_first_safe_axis_tangent_le
    (c : NewtonianPointSource) (x h : Vec3) (d : ℝ)
    (hd : 0 < d) (hx : d ≤ |x 0|) (hh : h 0 = 0) :
    ‖(fderiv ℝ c.accelerationField x) h‖ ≤
      ((1 / d ^ 3) *
        (c.gravitationalParameter * (5 / 4 : ℝ))) * ‖h‖ := by sorry
