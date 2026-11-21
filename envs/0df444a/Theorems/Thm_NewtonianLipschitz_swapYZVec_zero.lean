-- Prove2me | Theorems.Thm_NewtonianLipschitz_swapYZVec_zero
-- name    : NewtonianLipschitz.swapYZVec_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:27:51.123562+00:00
-- url     : https://prove2.me/theorems/64d58d82-0131-4755-9e87-4f99f3b68f93
-- title:
--   Newtonian Lipschitz: swap YZVec zero
-- statement:
--   The Newtonian Lipschitz construction uses the swap YZVec zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianPermutations.lean#L87-L87
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianPermutations.lean#L87-L87

module
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.swapYZVec_zero (x : Vec3) : swapYZVec x 0 = x 0 := by sorry

attribute [defeq] NewtonianLipschitz.swapYZVec_zero
