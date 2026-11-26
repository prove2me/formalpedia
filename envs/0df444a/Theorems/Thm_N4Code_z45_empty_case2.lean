-- Prove2me | Theorems.Thm_N4Code_z45_empty_case2
-- name    : N4Code.z45_empty_case2
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:22:03.010536+00:00
-- url     : https://prove2.me/theorems/c305ea57-df16-43c4-88fd-f8df7e16df7b
-- title:
--   N4 Code: z45 empty case2
-- statement:
--   The N4 Code construction uses the z45 empty case2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2299-L2478
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2299-L2478

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.z45_empty_case2 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (h07 : Columns07 C)
    (hcase : Odd (count C 3) ∧ Even (count C 2) ∧ Even (count C 4) ∧ Even (count C 5)) :
    ((∀ y : Word n, ¬ Z41 C t₁ t₂ y ∧ ¬ Z5 C t₁ t₂ y) ↔
      count C 1 = 1 ∧ count C 7 = 1 ∧ count C 2 = 0 ∧ count C 4 = 0 ∧
        count C 6 = 0 ∧ Odd (count C 3) ∧ Even (count C 5)) := by sorry
