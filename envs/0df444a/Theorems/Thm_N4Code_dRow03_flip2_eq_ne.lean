-- Prove2me | Theorems.Thm_N4Code_dRow03_flip2_eq_ne
-- name    : N4Code.dRow03_flip2_eq_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:18:24.766882+00:00
-- url     : https://prove2.me/theorems/e3bbe5cb-5576-5afc-b4b3-a8990f3f59a7
-- title:
--   N4 Code: d Row03 flip2 eq ne
-- statement:
--   Rows 0 and 3 are unchanged under F₂ when y t₁ ≠ y t₂.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L190-L218
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L190-L218

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.dRow03_flip2_eq_ne {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n) (hyne : y t₁ ≠ y t₂) :
    dRow C 0 (flipTwoBits t₁ t₂ y) = dRow C 0 y ∧
      dRow C 3 (flipTwoBits t₁ t₂ y) = dRow C 3 y := by sorry
