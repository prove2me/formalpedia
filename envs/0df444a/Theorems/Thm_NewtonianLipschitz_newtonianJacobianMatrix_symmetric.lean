-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_symmetric
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_symmetric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:43:46.771167+00:00
-- url     : https://prove2.me/theorems/7a31124d-b323-4c6c-8778-f03d1958704e
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix symmetric
-- statement:
--   The exact Newtonian Jacobian matrix is symmetric.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianMatrix.lean#L42-L59
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianMatrix.lean#L42-L59

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

theorem NewtonianLipschitz.newtonianJacobianMatrix_symmetric
    (μ : ℝ) (x : Vec3) :
    (newtonianJacobianMatrix μ x).IsSymm := by sorry
