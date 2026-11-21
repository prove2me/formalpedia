-- Prove2me | Theorems.Thm_NewtonianLipschitz_dominantRowNumerator_diagonal
-- name    : NewtonianLipschitz.dominantRowNumerator_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:29:31.519504+00:00
-- url     : https://prove2.me/theorems/fda81c77-d4bf-45b2-9f20-b2dc587c755b
-- title:
--   Newtonian Lipschitz: dominant Row Numerator diagonal
-- statement:
--   Diagonal restriction giving the exact candidate numerator.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianRows.lean#L139-L142
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianRows.lean#L139-L142

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_JacobianRows
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.dominantRowNumerator_diagonal (t : ℝ) :
    dominantRowNumerator t t = 2 + 6 * t - 2 * t ^ 2 := by sorry
