-- Prove2me | Theorems.Thm_N4Code_hammingDist_row1_row2_eq
-- name    : N4Code.hammingDist_row1_row2_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:18:34.083898+00:00
-- url     : https://prove2.me/theorems/7edf2426-f811-4c78-91a6-f883181fdb50
-- title:
--   N4 Code: hamming Dist row1 row2 eq
-- statement:
--   w(c₂ ⊕ c₃) = |2|+|3|+|4|+|5| for a Columns07 code (paper eq. w4, published (28)).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L868-L892
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L868-L892

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.hammingDist_row1_row2_eq {n : ℕ} (C : Code n) (h07 : Columns07 C) :
    hammingDist (row1 C) (row2 C) = count C 2 + count C 3 + count C 4 + count C 5 := by sorry
