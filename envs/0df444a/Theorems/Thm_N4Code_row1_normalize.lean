-- Prove2me | Theorems.Thm_N4Code_row1_normalize
-- name    : N4Code.row1_normalize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:17.263295+00:00
-- url     : https://prove2.me/theorems/97916b5d-d009-5ce3-aae0-a614fedb010e
-- title:
--   N4 Code: row1 normalize
-- statement:
--   Row 1 of the normalized code is the XOR of the even pair.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2043-L2053
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2043-L2053

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.row1_normalize {n : ℕ} (C : Code n) (i j : Fin 4) (hij : i ≠ j) :
    row (normalizeCode C i j) 1 = bitXor (row C i) (row C j) := by sorry
