-- Prove2me | Theorems.Thm_NewtonianLipschitz_diagonalParameter_sq
-- name    : NewtonianLipschitz.diagonalParameter_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:25:43.180462+00:00
-- url     : https://prove2.me/theorems/a6eef2ad-a051-4258-a531-ec312e6c53b9
-- title:
--   Newtonian Lipschitz: diagonal Parameter sq
-- statement:
--   Exact squared-radius normalization of the diagonal parameter.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianRows.lean#L94-L102
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianRows.lean#L94-L102

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_JacobianRows
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.diagonalParameter_sq (u v : ℝ) :
    0 ≤ diagonalParameter u v ∧
      2 * (diagonalParameter u v) ^ 2 = u ^ 2 + v ^ 2 := by sorry
