-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_signed_max_le_candidateMaximum
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_signed_max_le_candidateMaximum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:35:20.790226+00:00
-- url     : https://prove2.me/theorems/b2ce25c8-012e-4fef-a295-269dd01887fd
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix signed max le candidate Maximum
-- statement:
--   A bound for every row of the actual Newtonian Jacobian,
--   with arbitrary signs and the maximum of absolute coordinates.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianSignedBounds.lean#L70-L101
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianSignedBounds.lean#L70-L101

module
public import Definitions.Def_NewtonianLipschitz_JacobianAxisBounds
public import Definitions.Def_NewtonianLipschitz_JacobianSignedBounds
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_signed_max_le_candidateMaximum
    (μ : ℝ) (x : Vec3) (i : Fin 3)
    (hμ : 0 ≤ μ)
    (hmax :
      0 < max (|x 0|) (max (|x 1|) (|x 2|))) :
    (∑ j : Fin 3, |newtonianJacobianMatrix μ x i j|) ≤
      (1 / (max (|x 0|) (max (|x 1|) (|x 2|))) ^ 3) *
        (μ * candidateMaximum) := by sorry
