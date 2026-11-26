-- Prove2me | Theorems.Thm_N4Code_col0_ne_of_colVal_356
-- name    : N4Code.col0_ne_of_colVal_356
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:16:20.341525+00:00
-- url     : https://prove2.me/theorems/3f4e3012-2387-4911-8fce-6366915128bc
-- title:
--   N4 Code: col0 ne of col Val 356
-- statement:
--   A column of type 3, 5, or 6 is not the zero column.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2825-L2829
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2825-L2829

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.col0_ne_of_colVal_356 {s : Column} (h : colVal s = 3 ∨ colVal s = 5 ∨ colVal s = 6) :
    s ≠ col0 := by sorry
