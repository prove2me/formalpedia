-- Prove2me | Theorems.Thm_N4Code_count_pos_of_colVal
-- name    : N4Code.count_pos_of_colVal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:17:40.068251+00:00
-- url     : https://prove2.me/theorems/d20b4ea6-2d6b-4929-b987-5d492516f24b
-- title:
--   N4 Code: count pos of col Val
-- statement:
--   A type-i column exists at position t, so |i| ≥ 1.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1456-L1460
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1456-L1460

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.count_pos_of_colVal {n : ℕ} (C : Code n) {i : ℕ} (t : Fin n) (h : colVal (C t) = i) :
    1 ≤ count C i := by sorry
