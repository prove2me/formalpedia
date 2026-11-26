-- Prove2me | Theorems.Thm_N4Code_count_eq_zero_of_16_le
-- name    : N4Code.count_eq_zero_of_16_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:58:31.387461+00:00
-- url     : https://prove2.me/theorems/b7576584-c059-458f-9444-1ef624ace1e6
-- title:
--   N4 Code: count eq zero of 16 le
-- statement:
--   Types 16 and above never occur as column types.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L130-L136
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L130-L136

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

theorem N4Code.count_eq_zero_of_16_le {n : ℕ} (C : Code n) {i : ℕ} (hi : 16 ≤ i) : count C i = 0 := by sorry
