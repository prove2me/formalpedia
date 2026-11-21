-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_unitAxis_fderiv_opNorm_eq_candidateMaximum
-- name    : NewtonianLipschitz.NewtonianPointSource.unitAxis_fderiv_opNorm_eq_candidateMaximum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:36:00.270696+00:00
-- url     : https://prove2.me/theorems/bc35eea8-0ada-4375-b728-3103a77a4e6e
-- title:
--   Newtonian Point Source: unit Axis fderiv op Norm eq candidate Maximum
-- statement:
--   The exact candidate maximum is attained by the
--   Cartesian operator norm of the genuine Newtonian derivative.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianOperatorWitness.lean#L90-L110
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianOperatorWitness.lean#L90-L110

module
public import Definitions.Def_NewtonianLipschitz_JacobianSharpWitness
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorWitness
set_option autoImplicit true
@[expose] public section
public section
open Matrix
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.unitAxis_fderiv_opNorm_eq_candidateMaximum :
    ‖fderiv ℝ NewtonianPointSource.unitAxis.accelerationField
      (normalizedVector candidateCriticalPoint candidateCriticalPoint)‖ =
        candidateMaximum := by sorry
