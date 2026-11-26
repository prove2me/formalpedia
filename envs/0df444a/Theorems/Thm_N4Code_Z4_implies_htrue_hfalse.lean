-- Prove2me | Theorems.Thm_N4Code_Z4_implies_htrue_hfalse
-- name    : N4Code.Z4_implies_htrue_hfalse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:17:50.568099+00:00
-- url     : https://prove2.me/theorems/13f506c4-3735-5639-ac99-e35fa06c0478
-- title:
--   N4 Code: Z4 implies htrue hfalse
-- statement:
--   y ∈ Z4 forces y t₁ = true, y t₂ = false.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L401-L417
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L401-L417

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.Z4_implies_htrue_hfalse {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) {y : Word n} (hy : Z4 C t₁ t₂ y) :
    y t₁ = true ∧ y t₂ = false := by sorry
