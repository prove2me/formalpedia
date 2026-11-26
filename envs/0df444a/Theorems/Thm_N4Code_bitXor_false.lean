-- Prove2me | Theorems.Thm_N4Code_bitXor_false
-- name    : N4Code.bitXor_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:57:46.629234+00:00
-- url     : https://prove2.me/theorems/f7d08c6e-3db6-452b-912d-99172af11a81
-- title:
--   N4 Code: bit Xor false
-- statement:
--   XOR with the zero word is the identity.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L46-L48
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L46-L48

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

theorem N4Code.bitXor_false {n : ℕ} (y : Word n) : bitXor (fun _ => false) y = y := by sorry
