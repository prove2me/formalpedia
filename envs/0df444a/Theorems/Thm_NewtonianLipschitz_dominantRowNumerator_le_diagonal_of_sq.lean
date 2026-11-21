-- Prove2me | Theorems.Thm_NewtonianLipschitz_dominantRowNumerator_le_diagonal_of_sq
-- name    : NewtonianLipschitz.dominantRowNumerator_le_diagonal_of_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:32:03.006316+00:00
-- url     : https://prove2.me/theorems/8b6586d6-e11d-432f-a382-7ca63e057b91
-- title:
--   Newtonian Lipschitz: dominant Row Numerator le diagonal of sq
-- statement:
--   The first-row numerator is maximized on the diagonal at fixed
--   sum of squares. No comparison of denominators is required here.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianRows.lean#L106-L120
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianRows.lean#L106-L120

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_JacobianRows
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.dominantRowNumerator_le_diagonal_of_sq
    (u v t : ℝ) (ht : 0 ≤ t)
    (hsq : 2 * t ^ 2 = u ^ 2 + v ^ 2) :
    dominantRowNumerator u v ≤ dominantRowNumerator t t := by sorry
