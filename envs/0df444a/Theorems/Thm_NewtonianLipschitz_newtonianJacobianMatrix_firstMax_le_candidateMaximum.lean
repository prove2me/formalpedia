-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_firstMax_le_candidateMaximum
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_firstMax_le_candidateMaximum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:29:44.395521+00:00
-- url     : https://prove2.me/theorems/a90d120a-b326-459c-af65-5bfc0c4c94dd
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix first Max le candidate Maximum
-- statement:
--   The sharp candidate bounds every row of the physical
--   Jacobian when X is the largest nonnegative coordinate.
--   This lemma alone is not the unrestricted 3D derivative
--   theorem, obtained later in R024–R027.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianNormalization.lean#L71-L106
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianNormalization.lean#L71-L106

module
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations
public import Definitions.Def_NewtonianLipschitz_JacobianNormalization
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_firstMax_le_candidateMaximum
    (μ : ℝ) (x : Vec3) (i : Fin 3)
    (hμ : 0 ≤ μ)
    (hx0 : 0 < x 0)
    (hx10 : 0 ≤ x 1) (hx1 : x 1 ≤ x 0)
    (hx20 : 0 ≤ x 2) (hx2 : x 2 ≤ x 0) :
    (∑ j : Fin 3, |newtonianJacobianMatrix μ x i j|) ≤
      (1 / (x 0) ^ 3) * (μ * candidateMaximum) := by sorry
