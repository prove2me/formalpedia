-- Prove2me | Theorems.Thm_N4Code_Columns07_normalize
-- name    : N4Code.Columns07_normalize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:11:33.94375+00:00
-- url     : https://prove2.me/theorems/7292d953-bae2-4b67-a313-f62562225a61
-- title:
--   N4 Code: Columns07 normalize
-- statement:
--   The normalized code has row 0 all zeros.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2056-L2061
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2056-L2061

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.Columns07_normalize {n : ℕ} (C : Code n) (i j : Fin 4) (hij : i ≠ j) :
    Columns07 (normalizeCode C i j) := by sorry
