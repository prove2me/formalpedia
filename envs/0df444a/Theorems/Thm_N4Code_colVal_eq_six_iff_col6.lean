-- Prove2me | Theorems.Thm_N4Code_colVal_eq_six_iff_col6
-- name    : N4Code.colVal_eq_six_iff_col6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:53:38.651804+00:00
-- url     : https://prove2.me/theorems/5c6e25b3-5f27-4a27-b894-d5d52386d923
-- title:
--   N4 Code: col Val eq six iff col6
-- statement:
--   A column has value 6 exactly when it is `col6`.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Definitions.lean#L434-L435
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Definitions.lean#L434-L435

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

theorem N4Code.colVal_eq_six_iff_col6 (c : Column) : colVal c = 6 ↔ c = col6 := by sorry
