-- Prove2me | Theorems.Thm_N4Code_bitXor_comm
-- name    : N4Code.bitXor_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:56:47.131406+00:00
-- url     : https://prove2.me/theorems/19315949-1d88-470b-8683-c06e9061a84a
-- title:
--   N4 Code: bit Xor comm
-- statement:
--   XOR is commutative.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L30-L32
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L30-L32

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

theorem N4Code.bitXor_comm {n : ℕ} (x y : Word n) : bitXor x y = bitXor y x := by sorry
