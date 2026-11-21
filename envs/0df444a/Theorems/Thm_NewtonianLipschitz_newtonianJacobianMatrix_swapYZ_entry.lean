-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_swapYZ_entry
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_swapYZ_entry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:34:49.094041+00:00
-- url     : https://prove2.me/theorems/9bb59c8f-2163-4dcf-8cc7-e559b231a096
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix swap YZ entry
-- statement:
--   The actual Newtonian Jacobian entries transform exactly
--   under a Y/Z axis transposition.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianPermutations.lean#L102-L110
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianPermutations.lean#L102-L110

module
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_swapYZ_entry
    (μ : ℝ) (x : Vec3) (i j : Fin 3) :
    newtonianJacobianMatrix μ (swapYZVec x) i j =
      newtonianJacobianMatrix μ x (swapYZIndex i) (swapYZIndex j) := by sorry
