-- Prove2me | Theorems.Thm_N4Code_count_replace_inc
-- name    : N4Code.count_replace_inc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:07:12.062608+00:00
-- url     : https://prove2.me/theorems/05d0c7f1-492c-409e-8d7a-376dc6e69688
-- title:
--   N4 Code: count replace inc
-- statement:
--   Replacing a column by a new type i raises |i| by one.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L50-L69
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L50-L69

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.count_replace_inc {n : ℕ} (C : Code n) (t : Fin n) (s' : Column) (i : ℕ)
    (hc : colVal (C t) ≠ i) (hi' : colVal s' = i) :
    count (replaceColumn C t s') i = count C i + 1 := by sorry
