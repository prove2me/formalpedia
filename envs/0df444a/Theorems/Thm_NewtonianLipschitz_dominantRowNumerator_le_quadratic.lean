-- Prove2me | Theorems.Thm_NewtonianLipschitz_dominantRowNumerator_le_quadratic
-- name    : NewtonianLipschitz.dominantRowNumerator_le_quadratic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:43:01.236908+00:00
-- url     : https://prove2.me/theorems/4db449e8-13b1-40b1-b705-7d0ae1186844
-- title:
--   Newtonian Lipschitz: dominant Row Numerator le quadratic
-- statement:
--   Completing two squares produces a simple rational quadratic cap.
--   This is only a numerator inequality; the later R030 theorem proves a physical finite-difference estimate on convex safe domains.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianRows.lean#L132-L136
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianRows.lean#L132-L136

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_JacobianRows
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.dominantRowNumerator_le_quadratic (u v : ℝ) :
    dominantRowNumerator u v ≤
      (13 : ℝ) / 5 + ((13 : ℝ) / 2) * (u ^ 2 + v ^ 2) := by sorry
