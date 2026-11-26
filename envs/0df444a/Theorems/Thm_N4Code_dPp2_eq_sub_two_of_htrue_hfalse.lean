-- Prove2me | Theorems.Thm_N4Code_dPp2_eq_sub_two_of_htrue_hfalse
-- name    : N4Code.dPp2_eq_sub_two_of_htrue_hfalse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:17:56.16136+00:00
-- url     : https://prove2.me/theorems/76c1fab4-9c8f-4d43-bd30-449c35dcbd21
-- title:
--   N4 Code: d Pp2 eq sub two of htrue hfalse
-- statement:
--   d_P' = d_P − 2 in the (t,f) orientation.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L976-L983
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L976-L983

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.dPp2_eq_sub_two_of_htrue_hfalse {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n)
    (hy1 : y t₁ = true) (hy2 : y t₂ = false) :
    dPp2 C t₁ t₂ y = dP C y - 2 := by sorry
