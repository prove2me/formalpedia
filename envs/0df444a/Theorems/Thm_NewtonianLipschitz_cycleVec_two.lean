-- Prove2me | Theorems.Thm_NewtonianLipschitz_cycleVec_two
-- name    : NewtonianLipschitz.cycleVec_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:27:06.85181+00:00
-- url     : https://prove2.me/theorems/a7462cee-3875-400e-acf8-f83f3c6277bd
-- title:
--   Newtonian Lipschitz: cycle Vec two
-- statement:
--   The Newtonian Lipschitz construction uses the cycle Vec two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianPermutations.lean#L42-L42
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianPermutations.lean#L42-L42

module
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.cycleVec_two (x : Vec3) : cycleVec x 2 = x 0 := by sorry

attribute [defeq] NewtonianLipschitz.cycleVec_two
