-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_swapYZ_rowSum
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_swapYZ_rowSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:53:36.023104+00:00
-- url     : https://prove2.me/theorems/47f6796e-6af6-4e2e-b252-2134373ad489
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix swap YZ row Sum
-- statement:
--   The sum of absolute matrix entries in each row is unchanged
--   up to relabeling when Y and Z are interchanged.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianPermutations.lean#L114-L122
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianPermutations.lean#L114-L122

module
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_swapYZ_rowSum
    (μ : ℝ) (x : Vec3) (i : Fin 3) :
    (∑ j : Fin 3, |newtonianJacobianMatrix μ (swapYZVec x) i j|) =
      ∑ j : Fin 3,
        |newtonianJacobianMatrix μ x (swapYZIndex i) j| := by sorry
