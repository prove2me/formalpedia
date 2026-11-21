-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_normalized_tangent_le
-- name    : NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_normalized_tangent_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:59:43.027192+00:00
-- url     : https://prove2.me/theorems/cd776ba0-1285-485d-af43-831c9baa1323
-- title:
--   Newtonian Point Source: acceleration Field fderiv normalized tangent le
-- statement:
--   The physical Frechet derivative, not a surrogate scalar,
--   satisfies the 5/4 tangent action estimate at (1,u,v), u,v>=0.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/PhysicalTangentialNormalized.lean#L245-L266
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/PhysicalTangentialNormalized.lean#L245-L266

module
public import Definitions.Def_NewtonianLipschitz_SafePlaneReduction
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialNormalized
set_option autoImplicit true
@[expose] public section
public section
open Matrix
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_normalized_tangent_le
    (c : NewtonianPointSource) (u v : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : Vec3) (hzero : h 0 = 0) :
    ‖(fderiv ℝ c.accelerationField
      (normalizedVector u v)) h‖ ≤
      (c.gravitationalParameter * (5 / 4 : ℝ)) * ‖h‖ := by sorry
