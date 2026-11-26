-- Prove2me | Theorems.Thm_N4Code_twobitCount_replace_0_5
-- name    : N4Code.twobitCount_replace_0_5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:16:18.85145+00:00
-- url     : https://prove2.me/theorems/d1047dbb-1bbb-4c73-a71e-098ea967b70e
-- title:
--   N4 Code: twobit Count replace 0 5
-- statement:
--   Replacing a zero column by the type-5 column adds one two-bit column.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2782-L2814
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2782-L2814

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.twobitCount_replace_0_5 {n : ℕ} (C : Code n) (t : Fin n) (h0 : C t = col0) :
    twobitCount (replaceColumn C t col5) = twobitCount C + 1 := by sorry
