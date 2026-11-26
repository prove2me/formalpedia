-- Prove2me | Theorems.Thm_OpenQuantumProblem35_isConstantConfig_permute_iff
-- name    : OpenQuantumProblem35.isConstantConfig_permute_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:59:42.959398+00:00
-- url     : https://prove2.me/theorems/0f771aee-812f-4c3b-8876-f4c08d20ed6c
-- title:
--   Open Quantum Problem35: is Constant Config permute iff
-- statement:
--   Permuting the parties preserves the property of being a constant configuration.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L433-L440
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L433-L440

module
public import Mathlib
public import Definitions.Def_AME125_Defs
set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35

theorem OpenQuantumProblem35.isConstantConfig_permute_iff {n d : ℕ} (π : Equiv.Perm (Fin n)) (x : Config n d) :
    IsConstantConfig (permuteConfig π x) ↔ IsConstantConfig x := by sorry
