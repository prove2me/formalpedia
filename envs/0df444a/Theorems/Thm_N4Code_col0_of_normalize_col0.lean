-- Prove2me | Theorems.Thm_N4Code_col0_of_normalize_col0
-- name    : N4Code.col0_of_normalize_col0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:24:52.212312+00:00
-- url     : https://prove2.me/theorems/f73fbd1e-3007-5d3d-bdf8-bae3648e7c72
-- title:
--   N4 Code: col0 of normalize col0
-- statement:
--   If normalization leaves a zero column with flip disabled, the original
--   column is zero.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2225-L2235
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2225-L2235

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.col0_of_normalize_col0 {n : ℕ} (C : Code n) (i j : Fin 4) (t : Fin n)
    (h0n : (normalizeCode C i j) t = col0) (hf : (row C i) t = false) : C t = col0 := by sorry
