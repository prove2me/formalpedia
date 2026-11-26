-- Prove2me | Theorems.Thm_N4Code_tableZ_bounds
-- name    : N4Code.tableZ_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:19:48.641891+00:00
-- url     : https://prove2.me/theorems/2d5168b2-39de-55ef-826d-73a452e52368
-- title:
--   N4 Code: table Z bounds
-- statement:
--   Feasibility of a table assignment.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1469-L1496
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1469-L1496

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.tableZ_bounds {n : ℕ} (C : Code n) (a1 a2 a3 a4 a5 a6 a7 : ℕ)
    (h1 : a1 ≤ count C 1) (h2 : a2 ≤ count C 2) (h3 : a3 ≤ count C 3)
    (h4 : a4 ≤ count C 4) (h5 : a5 ≤ count C 5) (h6 : a6 ≤ count C 6)
    (h7 : a7 ≤ count C 7) :
    ∀ i ∈ Finset.Icc 0 15, tableZ a1 a2 a3 a4 a5 a6 a7 i ≤ count C i := by sorry
