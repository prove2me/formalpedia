-- Prove2me | Theorems.Thm_N4Code_Columns07_le7
-- name    : N4Code.Columns07_le7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:15.335954+00:00
-- url     : https://prove2.me/theorems/a8783b81-dc94-5aa9-a558-e49ade7b786c
-- title:
--   N4 Code: Columns07 le7
-- statement:
--   Columns07 means all type numbers are at most 7.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1091-L1116
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1091-L1116

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.Columns07_le7 {n : ℕ} (C : Code n) (h : Columns07 C) (t : Fin n) : colVal (C t) ≤ 7 := by sorry
