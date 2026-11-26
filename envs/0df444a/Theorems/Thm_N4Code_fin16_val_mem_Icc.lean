-- Prove2me | Theorems.Thm_N4Code_fin16_val_mem_Icc
-- name    : N4Code.fin16_val_mem_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:56:34.774784+00:00
-- url     : https://prove2.me/theorems/4d4c8892-f153-4dde-bc91-5947f5d18c55
-- title:
--   N4 Code: fin16 val mem Icc
-- statement:
--   The value of a `Fin 16` element lies in `0..15`.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L402-L404
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L402-L404

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

theorem N4Code.fin16_val_mem_Icc (a : Fin 16) : a.val ∈ Finset.Icc 0 15 := by sorry
