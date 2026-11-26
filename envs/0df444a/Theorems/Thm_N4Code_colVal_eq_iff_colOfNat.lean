-- Prove2me | Theorems.Thm_N4Code_colVal_eq_iff_colOfNat
-- name    : N4Code.colVal_eq_iff_colOfNat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:53:30.652728+00:00
-- url     : https://prove2.me/theorems/8c05f41a-7b1f-455d-ae52-8e2eb2b23bc3
-- title:
--   N4 Code: col Val eq iff col Of Nat
-- statement:
--   The type-number function is injective on the 4-bit range.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Definitions.lean#L409-L415
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Definitions.lean#L409-L415

import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_N4Code_Definitions
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.colVal_eq_iff_colOfNat (c : Column) (k : ℕ) (hk : k ≤ 15) :
    colVal c = k ↔ c = colOfNat k := by sorry
