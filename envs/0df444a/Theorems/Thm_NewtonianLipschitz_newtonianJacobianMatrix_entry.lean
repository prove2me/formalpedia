-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_entry
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_entry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:23:25.487406+00:00
-- url     : https://prove2.me/theorems/a22d08ba-61c0-4323-8091-a65067015ebf
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix entry
-- statement:
--   Cartesian entries of the exact point-source Jacobian.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianMatrix.lean#L110-L119
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianMatrix.lean#L110-L119

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

theorem NewtonianLipschitz.newtonianJacobianMatrix_entry
    (μ : ℝ) (x : Vec3) (i j : Fin 3) :
    newtonianJacobianMatrix μ x i j =
      (μ / euclideanRadius x ^ 5) *
        (3 * x i * x j -
          euclideanRadius x ^ 2 * (if i = j then 1 else 0)) := by sorry
