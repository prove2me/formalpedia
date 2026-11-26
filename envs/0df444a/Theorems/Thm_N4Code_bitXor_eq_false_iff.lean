-- Prove2me | Theorems.Thm_N4Code_bitXor_eq_false_iff
-- name    : N4Code.bitXor_eq_false_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:56:47.678498+00:00
-- url     : https://prove2.me/theorems/43a75658-c5de-4c9a-8d5c-2411b6353eac
-- title:
--   N4 Code: bit Xor eq false iff
-- statement:
--   XOR is zero exactly when the words agree.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L51-L60
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L51-L60

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

theorem N4Code.bitXor_eq_false_iff {n : ℕ} (x y : Word n) : (bitXor x y = fun _ => false) ↔ x = y := by sorry
