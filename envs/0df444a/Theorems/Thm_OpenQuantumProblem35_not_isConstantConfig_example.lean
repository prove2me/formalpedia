-- Prove2me | Theorems.Thm_OpenQuantumProblem35_not_isConstantConfig_example
-- name    : OpenQuantumProblem35.not_isConstantConfig_example
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:00:49.220028+00:00
-- url     : https://prove2.me/theorems/81ef6d3c-ebf5-58bb-9af8-aac4fb886dc9
-- title:
--   Open Quantum Problem35: not is Constant Config example
-- statement:
--   A simple binary two-party configuration with different entries is not constant.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L314-L318
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L314-L318

module
public import Mathlib
public import Definitions.Def_AME125_Defs
set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35

theorem OpenQuantumProblem35.not_isConstantConfig_example :
    ¬ IsConstantConfig (fun i : Fin 2 => if i = 0 then (0 : Fin 2) else 1) := by sorry
