-- Prove2me | Theorems.Thm_N4Code_dRow12_flip2_add_two
-- name    : N4Code.dRow12_flip2_add_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:18:16.714566+00:00
-- url     : https://prove2.me/theorems/4fd2aa33-4ab2-54a8-a6ac-da1abc3edb5e
-- title:
--   N4 Code: d Row12 flip2 add two
-- statement:
--   Row distances of the changed rows (1 and 2) rise by two when
--   (y t₁ = false, y t₂ = true) — paper eq. (thm2a).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L172-L187
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L172-L187

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.dRow12_flip2_add_two {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n)
    (hy1 : y t₁ = false) (hy2 : y t₂ = true) :
    dRow C 1 (flipTwoBits t₁ t₂ y) = dRow C 1 y + 2 ∧
      dRow C 2 (flipTwoBits t₁ t₂ y) = dRow C 2 y + 2 := by sorry
