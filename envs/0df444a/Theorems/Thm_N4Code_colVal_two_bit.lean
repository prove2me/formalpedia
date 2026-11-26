-- Prove2me | Theorems.Thm_N4Code_colVal_two_bit
-- name    : N4Code.colVal_two_bit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:11:38.144481+00:00
-- url     : https://prove2.me/theorems/3f95e02a-29ea-4d0b-9288-29e1845d8c02
-- title:
--   N4 Code: col Val two bit
-- statement:
--   A column with exactly two ones has type 3, 5, 6, 9, 10, or 12.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2139-L2152
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2139-L2152

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.colVal_two_bit (c : Column)
    (h : ∃ a b : Fin 4, a ≠ b ∧ (c = fun j : Fin 4 => j = a ∨ j = b)) :
    colVal c = 3 ∨ colVal c = 5 ∨ colVal c = 6 ∨ colVal c = 9 ∨ colVal c = 10 ∨ colVal c = 12 := by sorry
