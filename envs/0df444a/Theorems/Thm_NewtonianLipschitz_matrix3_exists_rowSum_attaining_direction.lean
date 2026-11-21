-- Prove2me | Theorems.Thm_NewtonianLipschitz_matrix3_exists_rowSum_attaining_direction
-- name    : NewtonianLipschitz.matrix3_exists_rowSum_attaining_direction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:35:39.680992+00:00
-- url     : https://prove2.me/theorems/84c6d518-14d0-4d23-ba86-f5d2d434f71f
-- title:
--   Newtonian Lipschitz: matrix3 exists row Sum attaining direction
-- statement:
--   Every absolute row sum of a real 3 by 3 matrix can be
--   attained in that row by a direction of Cartesian norm at most one.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianOperatorWitness.lean#L27-L47
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianOperatorWitness.lean#L27-L47

module
public import Definitions.Def_NewtonianLipschitz_JacobianSharpWitness
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorWitness
set_option autoImplicit true
@[expose] public section
public section
open Matrix
open NewtonianLipschitz

theorem NewtonianLipschitz.matrix3_exists_rowSum_attaining_direction
    (A : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    ∃ h : Vec3, ‖h‖ ≤ 1 ∧
      (A *ᵥ h) i = ∑ j : Fin 3, |A i j| := by sorry
