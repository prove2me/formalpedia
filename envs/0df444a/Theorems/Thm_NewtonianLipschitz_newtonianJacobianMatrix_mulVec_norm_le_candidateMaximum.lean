-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_mulVec_norm_le_candidateMaximum
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_mulVec_norm_le_candidateMaximum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:35:32.815967+00:00
-- url     : https://prove2.me/theorems/ba3d79a9-f40b-42a4-b164-aa6b686a5dcb
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix mul Vec norm le candidate Maximum
-- statement:
--   The true Newtonian Jacobian acts on any direction
--   with the candidate factor in the Cartesian supremum norm.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianOperatorAction.lean#L60-L85
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianOperatorAction.lean#L60-L85

module
public import Definitions.Def_NewtonianLipschitz_JacobianCartesianBound
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorAction
set_option autoImplicit true
@[expose] public section
public section
open Matrix
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_mulVec_norm_le_candidateMaximum
    (μ : ℝ) (x h : Vec3)
    (hμ : 0 ≤ μ) (hx : x ≠ 0) :
    ‖newtonianJacobianMatrix μ x *ᵥ h‖ ≤
      ((1 / ‖x‖ ^ 3) * (μ * candidateMaximum)) * ‖h‖ := by sorry
