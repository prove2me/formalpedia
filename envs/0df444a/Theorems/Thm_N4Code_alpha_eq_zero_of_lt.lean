-- Prove2me | Theorems.Thm_N4Code_alpha_eq_zero_of_lt
-- name    : N4Code.alpha_eq_zero_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:58:41.465974+00:00
-- url     : https://prove2.me/theorems/8b992e3c-d152-5455-a01a-ea49385f10d4
-- title:
--   N4 Code: alpha eq zero of lt
-- statement:
--   No word is at distance greater than n.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L244-L250
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L244-L250

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

theorem N4Code.alpha_eq_zero_of_lt {n : ℕ} (C : Code n) {d : ℕ} (hd : n < d) : alpha C d = 0 := by sorry
