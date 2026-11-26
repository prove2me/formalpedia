-- Prove2me | Theorems.Thm_N4Code_z4_empty_of_even
-- name    : N4Code.z4_empty_of_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:21:08.90713+00:00
-- url     : https://prove2.me/theorems/cf57c7f9-ae55-5085-9753-7cfe33b6aa71
-- title:
--   N4 Code: z4 empty of even
-- statement:
--   Lemma `lemma:y4` (Lemma 24): if w(c2 ⊕ c3) is even then Z4¹ is empty.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1070-L1093
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1070-L1093

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.z4_empty_of_even {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (h07 : Columns07 C)
    (h : Even (hammingDist (row1 C) (row2 C))) :
    ∀ y : Word n, ¬ Z41 C t₁ t₂ y := by sorry
