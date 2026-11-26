-- Prove2me | Theorems.Thm_N4Code_Z34_flip2_closed
-- name    : N4Code.Z34_flip2_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:20:34.124702+00:00
-- url     : https://prove2.me/theorems/be45f2f6-7a0b-4b0b-bdbd-ee23692bda71
-- title:
--   N4 Code: Z34 flip2 closed
-- statement:
--   F₂ maps Z3 ∪ Z4 into itself (paper eq. y34p).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L575-L711
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L575-L711

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.Z34_flip2_closed {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n) :
    (Z3 C t₁ t₂ y ∨ Z4 C t₁ t₂ y) →
      (Z3 C t₁ t₂ (flipTwoBits t₁ t₂ y) ∨ Z4 C t₁ t₂ (flipTwoBits t₁ t₂ y)) := by sorry
