-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_thirdMax_le_candidateMaximum
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_thirdMax_le_candidateMaximum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:35:34.812691+00:00
-- url     : https://prove2.me/theorems/f9bda8c2-7687-4649-a93d-19b5f9536bdf
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix third Max le candidate Maximum
-- statement:
--   Every row has the sharp candidate bound when Z is positive
--   and dominates the other two nonnegative Cartesian coordinates.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianAxisBounds.lean#L49-L80
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianAxisBounds.lean#L49-L80

module
public import Definitions.Def_NewtonianLipschitz_JacobianNormalization
public import Definitions.Def_NewtonianLipschitz_JacobianAxisBounds
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_thirdMax_le_candidateMaximum
    (μ : ℝ) (x : Vec3) (i : Fin 3)
    (hμ : 0 ≤ μ)
    (hx2 : 0 < x 2)
    (hx00 : 0 ≤ x 0) (hx0 : x 0 ≤ x 2)
    (hx10 : 0 ≤ x 1) (hx1 : x 1 ≤ x 2) :
    (∑ j : Fin 3, |newtonianJacobianMatrix μ x i j|) ≤
      (1 / (x 2) ^ 3) * (μ * candidateMaximum) := by sorry
