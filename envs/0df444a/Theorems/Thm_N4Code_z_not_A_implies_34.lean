-- Prove2me | Theorems.Thm_N4Code_z_not_A_implies_34
-- name    : N4Code.z_not_A_implies_34
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:20:29.287572+00:00
-- url     : https://prove2.me/theorems/962806a5-e23d-409f-b51c-9ef731959af9
-- title:
--   N4 Code: z not A implies 34
-- statement:
--   The complement of Z1 ∪ Z2 ∪ Z5 is Z3 ∪ Z4.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L522-L534
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L522-L534

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.z_not_A_implies_34 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) :
    ¬ (Z1 C t₁ t₂ y ∨ Z2 C t₁ t₂ y ∨ Z5 C t₁ t₂ y) → (Z3 C t₁ t₂ y ∨ Z4 C t₁ t₂ y) := by sorry
