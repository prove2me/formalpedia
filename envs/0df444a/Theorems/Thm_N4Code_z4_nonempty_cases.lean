-- Prove2me | Theorems.Thm_N4Code_z4_nonempty_cases
-- name    : N4Code.z4_nonempty_cases
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:21:31.980742+00:00
-- url     : https://prove2.me/theorems/e1034660-c916-42f1-abdd-e5d6f3c0c9f1
-- title:
--   N4 Code: z4 nonempty cases
-- statement:
--   The N4 Code construction uses the z4 nonempty cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1555-L1660
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1555-L1660

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.z4_nonempty_cases {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (h07 : Columns07 C)
    (_h : Odd (hammingDist (row1 C) (row2 C)))
    (hcase :
      (Odd (count C 2) ∧ Even (count C 3) ∧ Even (count C 4) ∧ Even (count C 5)) ∨
        (Odd (count C 2) ∧ Odd (count C 3) ∧ Odd (count C 4) ∧ Even (count C 5)) ∨
        (Odd (count C 2) ∧ Even (count C 3) ∧ Odd (count C 4) ∧ Odd (count C 5)) ∨
        (Even (count C 2) ∧ Odd (count C 3) ∧ Odd (count C 4) ∧ Odd (count C 5))) :
    ∃ y : Word n, Z41 C t₁ t₂ y := by sorry
