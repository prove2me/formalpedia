-- Prove2me | Theorems.Thm_N4Code_count_replace_dec
-- name    : N4Code.count_replace_dec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:07:08.241154+00:00
-- url     : https://prove2.me/theorems/15c8ee10-13b8-4259-8589-9c672e801509
-- title:
--   N4 Code: count replace dec
-- statement:
--   Replacing a column of type i by a different type lowers |i| by one.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L28-L47
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L28-L47

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.count_replace_dec {n : ℕ} (C : Code n) (t : Fin n) (s' : Column) (i : ℕ)
    (hc : colVal (C t) = i) (hi' : colVal s' ≠ i) :
    count (replaceColumn C t s') i = count C i - 1 := by sorry
