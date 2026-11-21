-- Prove2me | Theorems.Thm_NewtonianLipschitz_lateralRowNumerator_eq
-- name    : NewtonianLipschitz.lateralRowNumerator_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:26:09.774222+00:00
-- url     : https://prove2.me/theorems/9102ed47-8ce8-4645-b1c0-b431d96b334f
-- title:
--   Newtonian Lipschitz: lateral Row Numerator eq
-- statement:
--   Exported exact formula for the lateral-row numerator.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianRows.lean#L38-L41
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianRows.lean#L38-L41

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_JacobianRows
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.lateralRowNumerator_eq (u v : ℝ) :
    lateralRowNumerator u v =
      |2 * u ^ 2 - 1 - v ^ 2| + 3 * u * (1 + v) := by sorry
