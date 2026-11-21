-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_tangent_columns_le
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_normalized_tangent_columns_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:50:35.080641+00:00
-- url     : https://prove2.me/theorems/0ce42275-0d07-4e77-84b0-05103388e1da
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix normalized tangent columns le
-- statement:
--   The two tangent columns of the true Newtonian 3D Jacobian
--   have total absolute row sum at most 5*μ/4, even if u,v>1.
--   This is a physical matrix estimate, not just polynomial algebra.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/PhysicalTangentialNormalized.lean#L113-L204
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/PhysicalTangentialNormalized.lean#L113-L204

module
public import Definitions.Def_NewtonianLipschitz_SafePlaneReduction
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialNormalized
set_option autoImplicit true
@[expose] public section
public section
open Matrix
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_normalized_tangent_columns_le
    (μ u v : ℝ) (hμ : 0 ≤ μ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (k : Fin 3) :
    |newtonianJacobianMatrix μ (normalizedVector u v) k 1| +
      |newtonianJacobianMatrix μ (normalizedVector u v) k 2| ≤
        μ * (5 / 4 : ℝ) := by sorry
