-- Prove2me | Theorems.Thm_N4Code_exists_col0_of_count_pos
-- name    : N4Code.exists_col0_of_count_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:26.553798+00:00
-- url     : https://prove2.me/theorems/9c72da46-a8cc-56a5-83b6-2b1fbd5b4e3b
-- title:
--   N4 Code: exists col0 of count pos
-- statement:
--   A code with a 0-column has a position with the zero column.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2093-L2096
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2093-L2096

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.exists_col0_of_count_pos {n : ℕ} (C : Code n) (h : 1 ≤ count C 0) :
    ∃ t : Fin n, C t = col0 := by sorry
