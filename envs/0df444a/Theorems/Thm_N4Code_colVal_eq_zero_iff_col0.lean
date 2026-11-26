-- Prove2me | Theorems.Thm_N4Code_colVal_eq_zero_iff_col0
-- name    : N4Code.colVal_eq_zero_iff_col0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:09:50.795621+00:00
-- url     : https://prove2.me/theorems/f05dbc06-40ba-4294-b1f4-d40e6cef1ddb
-- title:
--   N4 Code: col Val eq zero iff col0
-- statement:
--   A column with type number 0 is the zero column.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1087-L1088
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1087-L1088

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.colVal_eq_zero_iff_col0 (c : Column) : colVal c = 0 ↔ c = col0 := by sorry
