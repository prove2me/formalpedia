-- Prove2me | Theorems.Thm_N4Code_bitXor_assoc
-- name    : N4Code.bitXor_assoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:58:08.851584+00:00
-- url     : https://prove2.me/theorems/1de1ec19-1085-4587-b1e1-624116924b65
-- title:
--   N4 Code: bit Xor assoc
-- statement:
--   XOR is associative.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L35-L38
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L35-L38

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

theorem N4Code.bitXor_assoc {n : ℕ} (x y z : Word n) : bitXor (bitXor x y) z = bitXor x (bitXor y z) := by sorry
