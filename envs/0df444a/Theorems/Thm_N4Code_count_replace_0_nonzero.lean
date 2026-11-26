-- Prove2me | Theorems.Thm_N4Code_count_replace_0_nonzero
-- name    : N4Code.count_replace_0_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:16:18.884692+00:00
-- url     : https://prove2.me/theorems/ea786d3d-fd88-5404-a5ac-a8abe0535b30
-- title:
--   N4 Code: count replace 0 nonzero
-- statement:
--   Replacing a zero column by a nonzero column decreases |0| by one.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2817-L2821
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2817-L2821

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.count_replace_0_nonzero {n : ℕ} (C : Code n) (t : Fin n) (s' : Column)
    (h0 : C t = col0) (hs : s' ≠ col0) :
    count (replaceColumn C t s') 0 = count C 0 - 1 := by sorry
