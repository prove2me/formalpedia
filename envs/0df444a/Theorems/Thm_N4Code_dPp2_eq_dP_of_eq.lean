-- Prove2me | Theorems.Thm_N4Code_dPp2_eq_dP_of_eq
-- name    : N4Code.dPp2_eq_dP_of_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:20:14.806291+00:00
-- url     : https://prove2.me/theorems/98fd7e61-443b-4b79-b579-4e83488d34c9
-- title:
--   N4 Code: d Pp2 eq d P of eq
-- statement:
--   d_P' = d_P when y t₁ = y t₂ (paper eq. thm2b).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L254-L258
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L254-L258

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.dPp2_eq_dP_of_eq {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n) (hyeq : y t₁ = y t₂) :
    dPp2 C t₁ t₂ y = dP C y := by sorry
