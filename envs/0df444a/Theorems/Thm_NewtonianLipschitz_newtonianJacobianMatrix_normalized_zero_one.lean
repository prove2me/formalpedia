-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_zero_one
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_normalized_zero_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:29:38.366783+00:00
-- url     : https://prove2.me/theorems/1747ddf5-a2ba-4710-9589-de0a097c7951
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix normalized zero one
-- statement:
--   First off-diagonal entry of the maximal-coordinate row.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianMatrix.lean#L158-L164
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianMatrix.lean#L158-L164

module
public import Definitions.Def_NewtonianLipschitz_Derivative
public import Definitions.Def_NewtonianLipschitz_JacobianRows
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
set_option autoImplicit true
@[expose] public section
public section
open Matrix WithLp
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_normalized_zero_one
    (μ u v : ℝ) :
    newtonianJacobianMatrix μ (normalizedVector u v) 0 1 =
      (μ / euclideanRadius (normalizedVector u v) ^ 5) *
        (3 * u) := by sorry
