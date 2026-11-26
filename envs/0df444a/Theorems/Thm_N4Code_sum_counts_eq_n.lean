-- Prove2me | Theorems.Thm_N4Code_sum_counts_eq_n
-- name    : N4Code.sum_counts_eq_n
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:58:26.797326+00:00
-- url     : https://prove2.me/theorems/e8a20c91-e92f-4ce0-9c3b-b4966cd4940b
-- title:
--   N4 Code: sum counts eq n
-- statement:
--   The counts of all 16 column types sum to n (paper §2.1).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L139-L147
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L139-L147

import Definitions.Def_N4Code_Definitions
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Definitions.Def_N4Code_Basic
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
open N4Code

theorem N4Code.sum_counts_eq_n {n : ℕ} (C : Code n) : (∑ i ∈ Finset.Icc 0 15, count C i) = n := by sorry
