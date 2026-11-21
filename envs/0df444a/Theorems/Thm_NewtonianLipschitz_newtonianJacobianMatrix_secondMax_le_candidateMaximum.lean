-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_secondMax_le_candidateMaximum
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_secondMax_le_candidateMaximum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:35:02.04557+00:00
-- url     : https://prove2.me/theorems/becc18b0-0f86-45a6-acec-bd92c4778dcd
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix second Max le candidate Maximum
-- statement:
--   Every row has the sharp candidate bound when Y is positive
--   and dominates the other two nonnegative Cartesian coordinates.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianAxisBounds.lean#L20-L45
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianAxisBounds.lean#L20-L45

module
public import Definitions.Def_NewtonianLipschitz_JacobianNormalization
public import Definitions.Def_NewtonianLipschitz_JacobianAxisBounds
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_secondMax_le_candidateMaximum
    (μ : ℝ) (x : Vec3) (i : Fin 3)
    (hμ : 0 ≤ μ)
    (hx1 : 0 < x 1)
    (hx00 : 0 ≤ x 0) (hx0 : x 0 ≤ x 1)
    (hx20 : 0 ≤ x 2) (hx2 : x 2 ≤ x 1) :
    (∑ j : Fin 3, |newtonianJacobianMatrix μ x i j|) ≤
      (1 / (x 1) ^ 3) * (μ * candidateMaximum) := by sorry
