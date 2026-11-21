-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_norm_le_candidateMaximum
-- name    : NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_norm_le_candidateMaximum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:35:44.813544+00:00
-- url     : https://prove2.me/theorems/ceff909d-d354-42ad-92eb-e88e3ca4437d
-- title:
--   Newtonian Point Source: acceleration Field fderiv norm le candidate Maximum
-- statement:
--   The genuine Frechet derivative has the same candidate
--   directional bound as the exact physical Jacobian matrix.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianOperatorAction.lean#L89-L96
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianOperatorAction.lean#L89-L96

module
public import Definitions.Def_NewtonianLipschitz_JacobianCartesianBound
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorAction
set_option autoImplicit true
@[expose] public section
public section
open Matrix
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_norm_le_candidateMaximum
    (c : NewtonianPointSource) (x h : Vec3) (hx : x ≠ 0) :
    ‖(fderiv ℝ c.accelerationField x) h‖ ≤
      ((1 / ‖x‖ ^ 3) *
        (c.gravitationalParameter * candidateMaximum)) * ‖h‖ := by sorry
