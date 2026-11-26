-- Prove2me | Theorems.Thm_N4Code_strict_better_two_bit_col0
-- name    : N4Code.strict_better_two_bit_col0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:15:57.51816+00:00
-- url     : https://prove2.me/theorems/02878f79-0493-572c-a8ca-d1df98d14c12
-- title:
--   N4 Code: strict better two bit col0
-- statement:
--   From a strict improvement by a two-bit column at a zero column, get a
--   strict improvement by a column of type 3, 5, or 6.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2493-L2529
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2493-L2529

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.strict_better_two_bit_col0 {n : ℕ} (C : Code n) (t : Fin n) (_h0 : C t = col0)
    (s₀ : Column)
    (hs₀ : colVal s₀ = 3 ∨ colVal s₀ = 5 ∨ colVal s₀ = 6 ∨
      colVal s₀ = 9 ∨ colVal s₀ = 10 ∨ colVal s₀ = 12)
    (hstrict : UniversalStrictBetter (replaceColumn C t s₀) C) :
    ∃ s' : Column, (colVal s' = 3 ∨ colVal s' = 5 ∨ colVal s' = 6) ∧
      UniversalStrictBetter (replaceColumn C t s') C := by sorry
