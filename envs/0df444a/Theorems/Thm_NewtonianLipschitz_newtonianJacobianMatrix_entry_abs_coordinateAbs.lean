-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_entry_abs_coordinateAbs
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_entry_abs_coordinateAbs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:30:04.949045+00:00
-- url     : https://prove2.me/theorems/6735e162-90a0-4102-b1c7-69aa7bba34ca
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix entry abs coordinate Abs
-- statement:
--   Every absolute matrix entry is unaffected by changing the signs
--   of any subset of the three Cartesian coordinates.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianSymmetries.lean#L55-L63
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianSymmetries.lean#L55-L63

module
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_entry_abs_coordinateAbs
    (μ : ℝ) (x : Vec3) (i j : Fin 3) :
    |newtonianJacobianMatrix μ (coordinateAbs x) i j| =
      |newtonianJacobianMatrix μ x i j| := by sorry
