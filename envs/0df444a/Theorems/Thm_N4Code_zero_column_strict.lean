-- Prove2me | Theorems.Thm_N4Code_zero_column_strict
-- name    : N4Code.zero_column_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:15:59.682363+00:00
-- url     : https://prove2.me/theorems/778ddc5a-40a4-5aee-832b-8f55dd1743ed
-- title:
--   N4 Code: zero column strict
-- statement:
--   Theorem `thm:0column` (Theorem 6) (2): otherwise, for some s' ∈ {3,5,6}, replacing a
--   0-column strictly improves.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2613-L2644
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2613-L2644

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.zero_column_strict {n : ℕ} (C : Code n) (h0 : count C 0 ≥ 1)
    (hC0 : ¬ ∃ C0 : Code n, Equivalent C C0 ∧
      count C0 0 + count C0 5 + count C0 6 = n ∧
        Odd (count C0 5) ∧ Odd (count C0 6)) :
    ∃ t : Fin n, C t = col0 ∧ ∃ s' : Column,
      (colVal s' = 3 ∨ colVal s' = 5 ∨ colVal s' = 6) ∧
        UniversalStrictBetter (replaceColumn C t s') C := by sorry
