-- Prove2me | Theorems.Thm_OpenQuantumProblem35_eq_leftIndex_zero_or_eq_rightIndex
-- name    : OpenQuantumProblem35.eq_leftIndex_zero_or_eq_rightIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:00:02.321671+00:00
-- url     : https://prove2.me/theorems/8954f4a4-989c-4642-8e5a-e12ed00f916b
-- title:
--   Open Quantum Problem35: eq left Index zero or eq right Index
-- statement:
--   Every index in $\mathrm{Fin}\, n$ is either the unique left index or a right index when the left block has size $1$.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L465-L476
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L465-L476

module
public import Mathlib
public import Definitions.Def_AME125_Defs
set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35

theorem OpenQuantumProblem35.eq_leftIndex_zero_or_eq_rightIndex {n : ℕ} (hn : 1 ≤ n) (i : Fin n) :
    i = leftIndex (m := 1) (n := n) hn 0 ∨
      ∃ j : Fin (n - 1), i = rightIndex (m := 1) (n := n) hn j := by sorry
