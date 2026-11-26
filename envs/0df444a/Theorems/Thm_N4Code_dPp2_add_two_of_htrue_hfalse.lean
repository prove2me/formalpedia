-- Prove2me | Theorems.Thm_N4Code_dPp2_add_two_of_htrue_hfalse
-- name    : N4Code.dPp2_add_two_of_htrue_hfalse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:18:34.795081+00:00
-- url     : https://prove2.me/theorems/0723b6e3-983c-44ff-902b-d625d1a6e927
-- title:
--   N4 Code: d Pp2 add two of htrue hfalse
-- statement:
--   d_P' + 2 = d_P when (y t₁ = true, y t₂ = false).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L291-L296
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L291-L296

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.dPp2_add_two_of_htrue_hfalse {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n)
    (hy1 : y t₁ = true) (hy2 : y t₂ = false) :
    dPp2 C t₁ t₂ y + 2 = dP C y := by sorry
