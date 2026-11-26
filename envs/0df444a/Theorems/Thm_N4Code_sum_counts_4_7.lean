-- Prove2me | Theorems.Thm_N4Code_sum_counts_4_7
-- name    : N4Code.sum_counts_4_7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:16.021842+00:00
-- url     : https://prove2.me/theorems/f606b25d-424e-4e07-9687-317fbb204958
-- title:
--   N4 Code: sum counts 4 7
-- statement:
--   In a Columns07 code, |4|+|5|+|6|+|7| is the weight of row 2.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2064-L2090
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2064-L2090

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.sum_counts_4_7 {n : ℕ} (C : Code n) (h07 : Columns07 C) :
    count C 4 + count C 5 + count C 6 + count C 7 = hammingWeight (row C 1) := by sorry
