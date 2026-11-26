-- Prove2me | Theorems.Thm_N4Code_z45_empty_case3
-- name    : N4Code.z45_empty_case3
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:22:03.857496+00:00
-- url     : https://prove2.me/theorems/6bd98de1-c0d1-58a9-82f1-48b86f39bb1c
-- title:
--   N4 Code: z45 empty case3
-- statement:
--   The N4 Code construction uses the z45 empty case3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2484-L2668
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2484-L2668

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.z45_empty_case3 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (h07 : Columns07 C)
    (hcase : Odd (count C 5) ∧ Even (count C 2) ∧ Even (count C 3) ∧ Even (count C 4)) :
    ((∀ y : Word n, ¬ Z41 C t₁ t₂ y ∧ ¬ Z5 C t₁ t₂ y) ↔
      count C 1 = 1 ∧ count C 7 = 1 ∧ count C 2 = 0 ∧ count C 4 = 0 ∧
        count C 6 = 0 ∧ Even (count C 3) ∧ Odd (count C 5)) := by sorry
