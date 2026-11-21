-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_any_safe_axis_tangent_le
-- name    : NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_any_safe_axis_tangent_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:53:01.801931+00:00
-- url     : https://prove2.me/theorems/e87aeda4-54b5-4e22-8343-29ec2bf38db3
-- title:
--   Newtonian Point Source: acceleration Field fderiv any safe axis tangent le
-- statement:
--   The genuine Newtonian Frechet derivative has the
--   exact 5/4 directional factor on EVERY signed-safe axis,
--   for any real position and any positive clearance d.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/PhysicalTangentialAllAxes.lean#L164-L203
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/PhysicalTangentialAllAxes.lean#L164-L203

module
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialFirstAxis
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialAllAxes
set_option autoImplicit true
@[expose] public section
public section
open Matrix
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_any_safe_axis_tangent_le
    (c : NewtonianPointSource) (x h : Vec3) (d : ℝ)
    (hd : 0 < d) (i : Fin 3)
    (hx : d ≤ |x i|) (hh : h i = 0) :
    ‖(fderiv ℝ c.accelerationField x) h‖ ≤
      ((1 / d ^ 3) *
        (c.gravitationalParameter * (5 / 4 : ℝ))) * ‖h‖ := by sorry
