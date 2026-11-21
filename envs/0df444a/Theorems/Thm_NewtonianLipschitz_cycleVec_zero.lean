-- Prove2me | Theorems.Thm_NewtonianLipschitz_cycleVec_zero
-- name    : NewtonianLipschitz.cycleVec_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:26:46.795453+00:00
-- url     : https://prove2.me/theorems/8c57e82c-3ce5-4049-b954-a2696a5281f3
-- title:
--   Newtonian Lipschitz: cycle Vec zero
-- statement:
--   The Newtonian Lipschitz construction uses the cycle Vec zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianPermutations.lean#L40-L40
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianPermutations.lean#L40-L40

module
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.cycleVec_zero (x : Vec3) : cycleVec x 0 = x 1 := by sorry

attribute [defeq] NewtonianLipschitz.cycleVec_zero
