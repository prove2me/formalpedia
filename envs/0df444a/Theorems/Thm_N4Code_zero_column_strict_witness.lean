-- Prove2me | Theorems.Thm_N4Code_zero_column_strict_witness
-- name    : N4Code.zero_column_strict_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:15:53.802116+00:00
-- url     : https://prove2.me/theorems/cd475ed9-5514-4d9c-9b92-3229b4edfcf8
-- title:
--   N4 Code: zero column strict witness
-- statement:
--   A Y3c witness for the col5 split gives a strict improvement.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2451-L2455
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2451-L2455

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.zero_column_strict_witness {n : ℕ} (C : Code n) (t : Fin n) (hcol : C t = col0) :
    (∃ y : Word n, Y3c C col5 colZeros_col5_nonempty colOnes_col5_nonempty t y) →
      UniversalStrictBetter (replaceColumn C t col5) C := by sorry
