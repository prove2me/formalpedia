-- Prove2me | Theorems.Thm_N4Code_sum_alpha_eq_two_pow
-- name    : N4Code.sum_alpha_eq_two_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:00:18.269102+00:00
-- url     : https://prove2.me/theorems/82184453-43cd-4dde-bc39-c1a45b5ff704
-- title:
--   N4 Code: sum alpha eq two pow
-- statement:
--   The distance distribution partitions the 2^n words.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L253-L262
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L253-L262

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

theorem N4Code.sum_alpha_eq_two_pow {n : ℕ} (C : Code n) : (∑ d ∈ Finset.Icc 0 n, alpha C d) = 2 ^ n := by sorry
