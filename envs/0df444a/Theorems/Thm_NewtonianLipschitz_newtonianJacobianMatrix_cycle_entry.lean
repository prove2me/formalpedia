-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_cycle_entry
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_cycle_entry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:29:10.677492+00:00
-- url     : https://prove2.me/theorems/56474b47-a685-480c-93d6-14915adf706b
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix cycle entry
-- statement:
--   An exact entry is carried to the corresponding row and column
--   under a cyclic relabeling of the Cartesian coordinate axes.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianPermutations.lean#L55-L63
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianPermutations.lean#L55-L63

module
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_cycle_entry
    (μ : ℝ) (x : Vec3) (i j : Fin 3) :
    newtonianJacobianMatrix μ (cycleVec x) i j =
      newtonianJacobianMatrix μ x (cycleIndex i) (cycleIndex j) := by sorry
