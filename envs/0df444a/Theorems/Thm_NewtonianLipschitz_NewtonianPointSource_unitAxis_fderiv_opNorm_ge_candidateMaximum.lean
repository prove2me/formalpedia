-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_unitAxis_fderiv_opNorm_ge_candidateMaximum
-- name    : NewtonianLipschitz.NewtonianPointSource.unitAxis_fderiv_opNorm_ge_candidateMaximum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:36:31.57201+00:00
-- url     : https://prove2.me/theorems/b093121a-9a27-414f-bc9e-aac0762ee0fa
-- title:
--   Newtonian Point Source: unit Axis fderiv op Norm ge candidate Maximum
-- statement:
--   At the exact critical diagonal source displacement,
--   the true Newtonian derivative has operator norm at least C3.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianOperatorWitness.lean#L51-L86
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianOperatorWitness.lean#L51-L86

module
public import Definitions.Def_NewtonianLipschitz_JacobianSharpWitness
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorWitness
set_option autoImplicit true
@[expose] public section
public section
open Matrix
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.unitAxis_fderiv_opNorm_ge_candidateMaximum :
    candidateMaximum ≤
      ‖fderiv ℝ NewtonianPointSource.unitAxis.accelerationField
        (normalizedVector candidateCriticalPoint candidateCriticalPoint)‖ := by sorry
