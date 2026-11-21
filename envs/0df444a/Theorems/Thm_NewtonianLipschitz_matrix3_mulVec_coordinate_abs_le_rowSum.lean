-- Prove2me | Theorems.Thm_NewtonianLipschitz_matrix3_mulVec_coordinate_abs_le_rowSum
-- name    : NewtonianLipschitz.matrix3_mulVec_coordinate_abs_le_rowSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:35:26.200956+00:00
-- url     : https://prove2.me/theorems/f73ba1d3-0d10-4824-9eb6-48303bd3c706
-- title:
--   Newtonian Lipschitz: matrix3 mul Vec coordinate abs le row Sum
-- statement:
--   Each coordinate of a three-by-three matrix-vector product
--   is bounded by its row's absolute sum times the direction norm.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianOperatorAction.lean#L25-L56
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianOperatorAction.lean#L25-L56

module
public import Definitions.Def_NewtonianLipschitz_JacobianCartesianBound
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorAction
set_option autoImplicit true
@[expose] public section
public section
open Matrix
open NewtonianLipschitz

theorem NewtonianLipschitz.matrix3_mulVec_coordinate_abs_le_rowSum
    (A : Matrix (Fin 3) (Fin 3) ℝ) (h : Vec3) (i : Fin 3) :
    |(A *ᵥ h) i| ≤ (∑ j : Fin 3, |A i j|) * ‖h‖ := by sorry
