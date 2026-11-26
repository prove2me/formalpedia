-- Prove2me | Theorems.Thm_N4Code_Columns07_sum_counts
-- name    : N4Code.Columns07_sum_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:13:31.127363+00:00
-- url     : https://prove2.me/theorems/201eeab7-679e-436a-9423-aa675f2a54ef
-- title:
--   N4 Code: Columns07 sum counts
-- statement:
--   A Columns07 code has all its columns among types 0..7.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1451-L1486
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1451-L1486

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.Columns07_sum_counts {n : ℕ} (C : Code n) (h07 : Columns07 C) :
    (∑ i ∈ Finset.Icc 0 7, count C i) = n := by sorry
