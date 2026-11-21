-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_rowSum_le_candidateMaximum_norm
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_rowSum_le_candidateMaximum_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:32:05.049529+00:00
-- url     : https://prove2.me/theorems/5cbc9ebc-5b32-4688-b9df-6278dcf3b07f
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix row Sum le candidate Maximum norm
-- statement:
--   Every row of the true Newtonian Jacobian has the exact
--   candidate upper bound at an arbitrary nonzero displacement,
--   expressed in the Cartesian supremum norm.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianCartesianBound.lean#L31-L41
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianCartesianBound.lean#L31-L41

module
public import Definitions.Def_NewtonianLipschitz_JacobianSignedBounds
public import Definitions.Def_NewtonianLipschitz_JacobianCartesianBound
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_rowSum_le_candidateMaximum_norm
    (μ : ℝ) (x : Vec3) (i : Fin 3)
    (hμ : 0 ≤ μ) (hx : x ≠ 0) :
    (∑ j : Fin 3, |newtonianJacobianMatrix μ x i j|) ≤
      (1 / ‖x‖ ^ 3) * (μ * candidateMaximum) := by sorry
