-- Prove2me | Theorems.Thm_OpenQuantumProblem35_constantConfig_injective
-- name    : OpenQuantumProblem35.constantConfig_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:59:24.374599+00:00
-- url     : https://prove2.me/theorems/3b34f273-7548-52e2-82ab-dbb1fcaeb8ec
-- title:
--   Open Quantum Problem35: constant Config injective
-- statement:
--   On a nonempty index type, different constants give different constant configurations.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L347-L352
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L347-L352

module
public import Mathlib
public import Definitions.Def_AME125_Defs
set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35

theorem OpenQuantumProblem35.constantConfig_injective {n d : ℕ} (hn : 1 ≤ n) :
    Function.Injective (@constantConfig n d) := by sorry
