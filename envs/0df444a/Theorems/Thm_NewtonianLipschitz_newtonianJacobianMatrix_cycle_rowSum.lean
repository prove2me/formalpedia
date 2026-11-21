-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_cycle_rowSum
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_cycle_rowSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:30:14.454119+00:00
-- url     : https://prove2.me/theorems/b3a632d3-c0b8-45ad-803b-2ad10e580166
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix cycle row Sum
-- statement:
--   A cyclic permutation merely relabels the absolute row sums.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianPermutations.lean#L66-L74
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianPermutations.lean#L66-L74

module
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_cycle_rowSum
    (μ : ℝ) (x : Vec3) (i : Fin 3) :
    (∑ j : Fin 3, |newtonianJacobianMatrix μ (cycleVec x) i j|) =
      ∑ j : Fin 3,
        |newtonianJacobianMatrix μ x (cycleIndex i) j| := by sorry
