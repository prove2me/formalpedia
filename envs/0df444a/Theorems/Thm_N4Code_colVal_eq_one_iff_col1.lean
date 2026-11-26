-- Prove2me | Theorems.Thm_N4Code_colVal_eq_one_iff_col1
-- name    : N4Code.colVal_eq_one_iff_col1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:53:36.686622+00:00
-- url     : https://prove2.me/theorems/61a219a0-3dac-4152-9b69-38cabe16e46a
-- title:
--   N4 Code: col Val eq one iff col1
-- statement:
--   A column has value 1 exactly when it is `col1`.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Definitions.lean#L419-L420
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Definitions.lean#L419-L420

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

theorem N4Code.colVal_eq_one_iff_col1 (c : Column) : colVal c = 1 ↔ c = col1 := by sorry
