-- Prove2me | Theorems.Thm_N4Code_z5_empty_case16
-- name    : N4Code.z5_empty_case16
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:22:12.957384+00:00
-- url     : https://prove2.me/theorems/53f4d7be-73da-42a7-bd8c-7b3802255e1e
-- title:
--   N4 Code: z5 empty case16
-- statement:
--   The N4 Code construction uses the z5 empty case16 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2674-L2829
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2674-L2829

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.z5_empty_case16 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (h07 : Columns07 C)
    (hcase : Even (count C 2) ∧ Even (count C 4) ∧ Odd (count C 3) ∧ Odd (count C 5)) :
    ((∀ y : Word n, ¬ Z5 C t₁ t₂ y) ↔
      count C 1 = 1 ∧ count C 7 = 1 ∧ count C 2 = 0 ∧ count C 4 = 0 ∧
        count C 6 = 0 ∧ Odd (count C 3) ∧ Odd (count C 5)) := by sorry
