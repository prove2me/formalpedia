-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_unitAxis_exists_outward_attaining_direction
-- name    : NewtonianLipschitz.NewtonianPointSource.unitAxis_exists_outward_attaining_direction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:41:56.970423+00:00
-- url     : https://prove2.me/theorems/32ccaf46-8481-4e3d-b651-8e356d0a89b9
-- title:
--   Newtonian Point Source: unit Axis exists outward attaining direction
-- statement:
--   One can orient an attaining derivative direction
--   so that its first Cartesian coordinate is nonnegative.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/AdmissibleCriticalDirection.lean#L27-L41
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/AdmissibleCriticalDirection.lean#L27-L41

module
public import Definitions.Def_NewtonianLipschitz_DerivativeAttainingDirection
public import Definitions.Def_NewtonianLipschitz_AdmissibleCriticalDirection
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.unitAxis_exists_outward_attaining_direction :
    ∃ h : Vec3, ‖h‖ ≤ 1 ∧ 0 ≤ h 0 ∧
      ‖(fderiv ℝ NewtonianPointSource.unitAxis.accelerationField
        (normalizedVector candidateCriticalPoint candidateCriticalPoint)) h‖ =
          candidateMaximum := by sorry
