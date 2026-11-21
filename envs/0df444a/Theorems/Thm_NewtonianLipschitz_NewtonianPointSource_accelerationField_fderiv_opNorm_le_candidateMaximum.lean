-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_opNorm_le_candidateMaximum
-- name    : NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_opNorm_le_candidateMaximum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:33:21.959386+00:00
-- url     : https://prove2.me/theorems/79917be3-f644-4445-8248-a1f46a87895b
-- title:
--   Newtonian Point Source: acceleration Field fderiv op Norm le candidate Maximum
-- statement:
--   Candidate Cartesian operator-norm upper bound on the
--   actual Newtonian Frechet derivative at a nonzero displacement.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianOperatorNorm.lean#L21-L34
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianOperatorNorm.lean#L21-L34

module
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorAction
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorNorm
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_opNorm_le_candidateMaximum
    (c : NewtonianPointSource) (x : Vec3) (hx : x ≠ 0) :
    ‖fderiv ℝ c.accelerationField x‖ ≤
      (1 / ‖x‖ ^ 3) *
        (c.gravitationalParameter * candidateMaximum) := by sorry
