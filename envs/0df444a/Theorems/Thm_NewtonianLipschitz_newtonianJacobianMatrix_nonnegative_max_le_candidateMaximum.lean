-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_nonnegative_max_le_candidateMaximum
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_nonnegative_max_le_candidateMaximum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:35:22.455741+00:00
-- url     : https://prove2.me/theorems/e9e0259c-70bc-4fc6-8204-561b63df2127
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix nonnegative max le candidate Maximum
-- statement:
--   Each row of the physical Jacobian has the sharp candidate
--   bound for a nonnegative displacement with positive maximum.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianSignedBounds.lean#L22-L66
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianSignedBounds.lean#L22-L66

module
public import Definitions.Def_NewtonianLipschitz_JacobianAxisBounds
public import Definitions.Def_NewtonianLipschitz_JacobianSignedBounds
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_nonnegative_max_le_candidateMaximum
    (μ : ℝ) (x : Vec3) (i : Fin 3)
    (hμ : 0 ≤ μ)
    (h0 : 0 ≤ x 0) (h1 : 0 ≤ x 1) (h2 : 0 ≤ x 2)
    (hmax : 0 < max (x 0) (max (x 1) (x 2))) :
    (∑ j : Fin 3, |newtonianJacobianMatrix μ x i j|) ≤
      (1 / (max (x 0) (max (x 1) (x 2))) ^ 3) *
        (μ * candidateMaximum) := by sorry
