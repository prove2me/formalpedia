-- Prove2me | Theorems.Thm_N4Code_tableK_bounds_47
-- name    : N4Code.tableK_bounds_47
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:58.929347+00:00
-- url     : https://prove2.me/theorems/0dfec1c3-c7d2-5263-905a-8e058ba28f5c
-- title:
--   N4 Code: table K bounds 47
-- statement:
--   The table bounds restricted to types 4..7.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1442-L1448
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1442-L1448

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.tableK_bounds_47 {n : ℕ} (C : Code n) (a4 a5 a6 a7 : ℕ)
    (hcnt0 : 1 ≤ count C 0) (ha4 : a4 ≤ count C 4) (ha5 : a5 ≤ count C 5)
    (ha6 : a6 ≤ count C 6) (ha7 : a7 ≤ count C 7) :
    ∀ i ∈ Finset.Icc 4 7, tableK a4 a5 a6 a7 i ≤ count C i := by sorry
