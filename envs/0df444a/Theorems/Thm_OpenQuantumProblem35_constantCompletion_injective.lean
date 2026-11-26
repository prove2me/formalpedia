-- Prove2me | Theorems.Thm_OpenQuantumProblem35_constantCompletion_injective
-- name    : OpenQuantumProblem35.constantCompletion_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:59:56.72446+00:00
-- url     : https://prove2.me/theorems/e0aa97e4-dcc5-594e-92a1-c46885920d51
-- title:
--   Open Quantum Problem35: constant Completion injective
-- statement:
--   The completion map for constant configurations is injective once $n \ge 2$.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L479-L490
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L479-L490

module
public import Mathlib
public import Definitions.Def_AME125_Defs
set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35

theorem OpenQuantumProblem35.constantCompletion_injective {n d : ℕ} (hn : 2 ≤ n) :
    Function.Injective (@constantCompletion n d) := by sorry
