-- Prove2me | Theorems.Thm_N4Code_zero_column_strict_better
-- name    : N4Code.zero_column_strict_better
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:16:00.735221+00:00
-- url     : https://prove2.me/theorems/eec0d462-fb85-417e-b221-6c3fb01a8fd2
-- title:
--   N4 Code: zero column strict better
-- statement:
--   Theorem `thm:0column` (Theorem 6) engine, strict version: a Y3c witness gives a
--   strict improvement.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2415-L2448
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2415-L2448

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.zero_column_strict_better {n : ℕ} (C : Code n) (t : Fin n) (s' : Column)
    (hcol : C t = col0) (hO : (colZeros s').Nonempty) (hP : (colOnes s').Nonempty)
    (hy : ∃ y : Word n, Y3c C s' hO hP t y) :
    UniversalStrictBetter (replaceColumn C t s') C := by sorry
