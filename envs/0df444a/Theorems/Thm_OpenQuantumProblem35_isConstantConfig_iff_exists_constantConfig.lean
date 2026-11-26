-- Prove2me | Theorems.Thm_OpenQuantumProblem35_isConstantConfig_iff_exists_constantConfig
-- name    : OpenQuantumProblem35.isConstantConfig_iff_exists_constantConfig
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:59:26.825087+00:00
-- url     : https://prove2.me/theorems/5fbc8362-58bf-5c16-bd6e-3c608b9268dd
-- title:
--   Open Quantum Problem35: is Constant Config iff exists constant Config
-- statement:
--   A configuration on a nonempty index type is constant iff it is equal to some constant configuration.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L355-L365
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L355-L365

module
public import Mathlib
public import Definitions.Def_AME125_Defs
set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35

theorem OpenQuantumProblem35.isConstantConfig_iff_exists_constantConfig {n d : ℕ} (hn : 1 ≤ n)
    (x : Config n d) :
    IsConstantConfig x ↔ ∃ a : Fin d, x = constantConfig (m := n) (d := d) a := by sorry
