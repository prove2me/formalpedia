-- Prove2me | Theorems.Thm_N4Code_two_zero_columns
-- name    : N4Code.two_zero_columns
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:26:18.318595+00:00
-- url     : https://prove2.me/theorems/aac3cb8c-af36-5e8b-8572-5dbb60467ed2
-- title:
--   N4 Code: two zero columns
-- statement:
--   The N4 Code construction uses the two zero columns property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2841-L2933
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2841-L2933

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.two_zero_columns {n : ℕ} (C : Code n) (h : count C 0 ≥ 2) :
    ∃ t₁ t₂ : Fin n, t₁ ≠ t₂ ∧ C t₁ = col0 ∧ C t₂ = col0 ∧
      ∃ s₁ s₂ : Column,
        (colVal s₁ = 3 ∨ colVal s₁ = 5 ∨ colVal s₁ = 6) ∧
        (colVal s₂ = 3 ∨ colVal s₂ = 5 ∨ colVal s₂ = 6) ∧
          UniversalStrictBetter (replaceColumn (replaceColumn C t₁ s₁) t₂ s₂) C := by sorry
