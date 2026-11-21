-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_mulVec
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_mulVec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:32:27.770796+00:00
-- url     : https://prove2.me/theorems/0ceb8f32-90a2-4ef2-9f78-5725111d868e
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix mul Vec
-- statement:
--   Exact matrix action on a direction at any nonzero source separation.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianMatrix.lean#L62-L89
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianMatrix.lean#L62-L89

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

theorem NewtonianLipschitz.newtonianJacobianMatrix_mulVec
    (μ : ℝ) (x h : Vec3) (hx : x ≠ 0) :
    newtonianJacobianMatrix μ x *ᵥ h =
      (-(μ) / euclideanRadius x ^ 3) • h +
        ((3 * μ / euclideanRadius x ^ 5) * (x ⬝ᵥ h)) • x := by sorry
