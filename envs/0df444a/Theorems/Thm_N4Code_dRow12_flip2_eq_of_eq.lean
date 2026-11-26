-- Prove2me | Theorems.Thm_N4Code_dRow12_flip2_eq_of_eq
-- name    : N4Code.dRow12_flip2_eq_of_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:20:12.153797+00:00
-- url     : https://prove2.me/theorems/140c230e-783f-591c-9ce8-8eb4d3981b81
-- title:
--   N4 Code: d Row12 flip2 eq of eq
-- statement:
--   Rows 1 and 2 are unchanged under F₂ when y t₁ = y t₂ (paper eq. thm2b).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L221-L251
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L221-L251

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.dRow12_flip2_eq_of_eq {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n) (hyeq : y t₁ = y t₂) :
    dRow C 1 (flipTwoBits t₁ t₂ y) = dRow C 1 y ∧
      dRow C 2 (flipTwoBits t₁ t₂ y) = dRow C 2 y := by sorry
