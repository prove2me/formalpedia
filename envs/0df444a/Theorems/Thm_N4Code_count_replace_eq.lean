-- Prove2me | Theorems.Thm_N4Code_count_replace_eq
-- name    : N4Code.count_replace_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:07:10.492353+00:00
-- url     : https://prove2.me/theorems/6517b8e5-6ed7-4244-a9c7-d8d5b9d510b7
-- title:
--   N4 Code: count replace eq
-- statement:
--   Replacing a column by a different type leaves other counts unchanged.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L72-L91
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L72-L91

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.count_replace_eq {n : ℕ} (C : Code n) (t : Fin n) (s' : Column) (i : ℕ)
    (hc : colVal (C t) ≠ i) (hi' : colVal s' ≠ i) :
    count (replaceColumn C t s') i = count C i := by sorry
