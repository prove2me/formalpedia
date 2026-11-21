-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_unitAxis_fderiv_exists_attaining_direction
-- name    : NewtonianLipschitz.NewtonianPointSource.unitAxis_fderiv_exists_attaining_direction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:39:45.015697+00:00
-- url     : https://prove2.me/theorems/700c35c8-fdd0-45dd-8b37-6a65bbc0f583
-- title:
--   Newtonian Point Source: unit Axis fderiv exists attaining direction
-- statement:
--   The derivative at the unit-parameter critical diagonal
--   has a Cartesian direction of norm at most one whose
--   derivative action has norm equal to C3.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/DerivativeAttainingDirection.lean#L26-L82
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/DerivativeAttainingDirection.lean#L26-L82

module
public import Definitions.Def_NewtonianLipschitz_DerivativeCoefficientMinimality
public import Definitions.Def_NewtonianLipschitz_DerivativeAttainingDirection
set_option autoImplicit true
@[expose] public section
public section
open Matrix
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.unitAxis_fderiv_exists_attaining_direction :
    ∃ h : Vec3, ‖h‖ ≤ 1 ∧
      ‖(fderiv ℝ NewtonianPointSource.unitAxis.accelerationField
        (normalizedVector candidateCriticalPoint candidateCriticalPoint)) h‖ =
          candidateMaximum := by sorry
