-- Prove2me | Theorems.Thm_N4Code_witness_exists_C0form
-- name    : N4Code.witness_exists_C0form
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:13:50.247437+00:00
-- url     : https://prove2.me/theorems/6bd39121-7e9d-5f7f-833c-03b3e78832d8
-- title:
--   N4 Code: witness exists C0form
-- statement:
--   The parity table (paper Table 0column): for a Columns07 code that is not
--   in the C0 form, with W = |4|+|5|+|6|+|7| even, there is a Y3c witness for the
--   col5 split.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1595-L1889
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1595-L1889

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.witness_exists_C0form {n : ℕ} (C : Code n) (h07 : Columns07 C)
    (hcnt0 : 1 ≤ count C 0) (hWeven : Even (count C 4 + count C 5 + count C 6 + count C 7))
    (hnotC0 : ¬ C0form C) :
    ∃ t : Fin n, C t = col0 ∧ ∃ y : Word n, Y3c C col5 colZeros_col5_nonempty
      colOnes_col5_nonempty t y := by sorry
