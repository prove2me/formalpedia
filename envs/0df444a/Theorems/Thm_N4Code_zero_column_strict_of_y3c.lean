-- Prove2me | Theorems.Thm_N4Code_zero_column_strict_of_y3c
-- name    : N4Code.zero_column_strict_of_y3c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:16:33.247698+00:00
-- url     : https://prove2.me/theorems/8c560318-dbb7-4fe3-a5d8-79678384211a
-- title:
--   N4 Code: zero column strict of y3c
-- statement:
--   Nonempty `Y3c` forces strict improvement (paper `thm:0column` (Theorem 6) (2) engine).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L565-L596
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L565-L596

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.zero_column_strict_of_y3c {n : ℕ} (C : Code n) (t : Fin n) (s' : Column)
    (hcol : C t = col0) (hO : (colZeros s').Nonempty) (hP : (colOnes s').Nonempty)
    {y : Word n} (hy : Y3c C s' hO hP t y) :
    UniversalStrictBetter (replaceColumn C t s') C := by sorry
