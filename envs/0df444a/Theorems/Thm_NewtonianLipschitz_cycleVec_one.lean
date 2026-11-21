-- Prove2me | Theorems.Thm_NewtonianLipschitz_cycleVec_one
-- name    : NewtonianLipschitz.cycleVec_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:27:07.938913+00:00
-- url     : https://prove2.me/theorems/a7262401-4bd6-4112-b9a7-c2dd25209abc
-- title:
--   Newtonian Lipschitz: cycle Vec one
-- statement:
--   The Newtonian Lipschitz construction uses the cycle Vec one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianPermutations.lean#L41-L41
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianPermutations.lean#L41-L41

module
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.cycleVec_one (x : Vec3) : cycleVec x 1 = x 2 := by sorry

attribute [defeq] NewtonianLipschitz.cycleVec_one
