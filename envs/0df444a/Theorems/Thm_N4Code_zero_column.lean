-- Prove2me | Theorems.Thm_N4Code_zero_column
-- name    : N4Code.zero_column
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:13:10.93897+00:00
-- url     : https://prove2.me/theorems/6c14e0f2-dddb-4398-97c0-8af7b7ce9807
-- title:
--   N4 Code: zero column
-- statement:
--   The N4 Code construction uses the zero column property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L961-L1061
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L961-L1061

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.zero_column {n : ℕ} (C : Code n) (t : Fin n) (h0 : C t = col0)
    (hC0 : ∃ C0 : Code n, Equivalent C C0 ∧
      count C0 0 + count C0 5 + count C0 6 = n ∧
        Odd (count C0 5) ∧ Odd (count C0 6)) :
    ∀ s' : Column, UniversalEqual (replaceColumn C t s') C := by sorry
