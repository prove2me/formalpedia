-- Prove2me | Theorems.Thm_N4Code_count_eq_card
-- name    : N4Code.count_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:56:31.283695+00:00
-- url     : https://prove2.me/theorems/8cdde435-5f6f-4490-a4b3-d2ccf137f4f6
-- title:
--   N4 Code: count eq card
-- statement:
--   |i|_C as the number of type-i columns (cardinality form).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L125-L127
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L125-L127

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

theorem N4Code.count_eq_card {n : ℕ} (C : Code n) (i : ℕ) :
    count C i = (Finset.univ.filter fun t : Fin n => colVal (C t) = i).card := by sorry
