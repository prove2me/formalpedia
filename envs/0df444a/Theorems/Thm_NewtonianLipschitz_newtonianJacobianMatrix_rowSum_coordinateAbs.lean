-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_rowSum_coordinateAbs
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_rowSum_coordinateAbs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:34:24.752105+00:00
-- url     : https://prove2.me/theorems/830e1b18-f164-4291-9308-c7f690e2c7e7
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix row Sum coordinate Abs
-- statement:
--   Every row's sum of absolute values is invariant under replacing
--   the original coordinates by their absolute values.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianSymmetries.lean#L67-L73
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianSymmetries.lean#L67-L73

module
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_rowSum_coordinateAbs
    (μ : ℝ) (x : Vec3) (i : Fin 3) :
    (∑ j : Fin 3, |newtonianJacobianMatrix μ (coordinateAbs x) i j|) =
      ∑ j : Fin 3, |newtonianJacobianMatrix μ x i j| := by sorry
