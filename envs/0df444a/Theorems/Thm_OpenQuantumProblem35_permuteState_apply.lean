-- Prove2me | Theorems.Thm_OpenQuantumProblem35_permuteState_apply
-- name    : OpenQuantumProblem35.permuteState_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:58:49.005801+00:00
-- url     : https://prove2.me/theorems/f9120996-cf0d-520c-96fa-08dc5eb830d2
-- title:
--   Open Quantum Problem35: permute State apply
-- statement:
--   Evaluating a permuted state vector reads the amplitude at the permuted configuration.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L167-L169
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L167-L169

module
public import Mathlib
public import Definitions.Def_AME125_Defs
set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35

theorem OpenQuantumProblem35.permuteState_apply {n d : ℕ} (π : Equiv.Perm (Fin n)) (ψ : StateVector n d) (x : Config n d) :
    permuteState π ψ x = ψ (permuteConfig π x) := by sorry
