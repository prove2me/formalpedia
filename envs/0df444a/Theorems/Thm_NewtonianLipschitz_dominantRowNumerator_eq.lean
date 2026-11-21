-- Prove2me | Theorems.Thm_NewtonianLipschitz_dominantRowNumerator_eq
-- name    : NewtonianLipschitz.dominantRowNumerator_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:31:42.966715+00:00
-- url     : https://prove2.me/theorems/bb04ebeb-60b3-4bf7-8edd-f09e43b16e4f
-- title:
--   Newtonian Lipschitz: dominant Row Numerator eq
-- statement:
--   Public expression for the dominant numerator, usable from sealed
--   Lean modules that cannot unfold a separately compiled definition.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianRows.lean#L28-L30
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianRows.lean#L28-L30

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_JacobianRows
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.dominantRowNumerator_eq (u v : ℝ) :
    dominantRowNumerator u v = 2 - u ^ 2 - v ^ 2 + 3 * (u + v) := by sorry
