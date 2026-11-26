-- Prove2me | Theorems.Thm_N4Code_flipCol_col5_val
-- name    : N4Code.flipCol_col5_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:27.586964+00:00
-- url     : https://prove2.me/theorems/520f2e2e-7329-5d33-af93-b25aabd8d87c
-- title:
--   N4 Code: flip Col col5 val
-- statement:
--   Flipping the type-5 column gives the two-bit column with ones at 0 and 2.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2179-L2181
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2179-L2181

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.flipCol_col5_val (k : Fin 4) :
    (!(col5 k)) = decide (k = (0 : Fin 4) ∨ k = (2 : Fin 4)) := by sorry
