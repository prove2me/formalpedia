-- Prove2me | Theorems.Thm_N4Code_row_i_false_of_col0
-- name    : N4Code.row_i_false_of_col0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:24:54.795065+00:00
-- url     : https://prove2.me/theorems/a58964fa-b51d-5ebd-9348-f84e60bea752
-- title:
--   N4 Code: row i false of col0
-- statement:
--   A true zero column is never flipped during normalization.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2238-L2240
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2238-L2240

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.row_i_false_of_col0 {n : ℕ} (C : Code n) (i : Fin 4) (t : Fin n) (h0 : C t = col0) :
    (row C i) t = false := by sorry
