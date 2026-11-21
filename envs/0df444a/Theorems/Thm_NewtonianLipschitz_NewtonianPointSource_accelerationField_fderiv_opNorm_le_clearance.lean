-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_opNorm_le_clearance
-- name    : NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_opNorm_le_clearance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:35:56.637521+00:00
-- url     : https://prove2.me/theorems/9523f6d7-f031-49fd-9a55-ea0a8d86541d
-- title:
--   Newtonian Point Source: acceleration Field fderiv op Norm le clearance
-- statement:
--   Under positive Cartesian clearance, the Frechet
--   derivative's operator norm obeys the candidate cube bound.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianOperatorNorm.lean#L38-L60
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianOperatorNorm.lean#L38-L60

module
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorAction
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorNorm
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_opNorm_le_clearance
    (c : NewtonianPointSource) (x : Vec3) (d : ℝ)
    (hd : 0 < d) (hclear : d ≤ ‖x‖) :
    ‖fderiv ℝ c.accelerationField x‖ ≤
      (1 / d ^ 3) *
        (c.gravitationalParameter * candidateMaximum) := by sorry
