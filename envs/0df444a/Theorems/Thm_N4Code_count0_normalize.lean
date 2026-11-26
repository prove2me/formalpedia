-- Prove2me | Theorems.Thm_N4Code_count0_normalize
-- name    : N4Code.count0_normalize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:16.004935+00:00
-- url     : https://prove2.me/theorems/7f3987a9-b9aa-5912-8a25-1539e27a5895
-- title:
--   N4 Code: count0 normalize
-- statement:
--   The normalized code keeps a 0-column.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2099-L2115
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2099-L2115

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.count0_normalize {n : ℕ} (C : Code n) (i j : Fin 4) (_hij : i ≠ j)
    (h : 1 ≤ count C 0) : 1 ≤ count (normalizeCode C i j) 0 := by sorry
