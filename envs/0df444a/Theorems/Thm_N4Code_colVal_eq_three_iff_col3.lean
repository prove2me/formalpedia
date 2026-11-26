-- Prove2me | Theorems.Thm_N4Code_colVal_eq_three_iff_col3
-- name    : N4Code.colVal_eq_three_iff_col3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:53:36.457332+00:00
-- url     : https://prove2.me/theorems/1275beab-b647-5212-808a-f96d4b16737f
-- title:
--   N4 Code: col Val eq three iff col3
-- statement:
--   A column has value 3 exactly when it is `col3`.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Definitions.lean#L424-L425
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Definitions.lean#L424-L425

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

theorem N4Code.colVal_eq_three_iff_col3 (c : Column) : colVal c = 3 ↔ c = col3 := by sorry
