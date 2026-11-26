-- Prove2me | Theorems.Thm_N4Code_row0_normalize
-- name    : N4Code.row0_normalize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:14.692797+00:00
-- url     : https://prove2.me/theorems/6ab304ef-69a8-5b5f-94e2-ea9fe99ec426
-- title:
--   N4 Code: row0 normalize
-- statement:
--   Row 0 of the normalized code is all zeros.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2030-L2040
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2030-L2040

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.row0_normalize {n : ℕ} (C : Code n) (i j : Fin 4) (hij : i ≠ j) :
    row (normalizeCode C i j) 0 = (fun _ : Fin n => false) := by sorry
