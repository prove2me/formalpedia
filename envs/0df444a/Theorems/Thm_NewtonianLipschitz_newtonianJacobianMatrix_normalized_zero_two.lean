-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_zero_two
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_normalized_zero_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:29:40.905508+00:00
-- url     : https://prove2.me/theorems/2ec4f078-f79a-48f2-9b56-6adac380a615
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix normalized zero two
-- statement:
--   Second off-diagonal entry of the maximal-coordinate row.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianMatrix.lean#L167-L173
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianMatrix.lean#L167-L173

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

theorem NewtonianLipschitz.newtonianJacobianMatrix_normalized_zero_two
    (μ u v : ℝ) :
    newtonianJacobianMatrix μ (normalizedVector u v) 0 2 =
      (μ / euclideanRadius (normalizedVector u v) ^ 5) *
        (3 * v) := by sorry
