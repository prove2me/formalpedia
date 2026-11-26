-- Prove2me | Theorems.Thm_N4Code_dOp2_le_dO_of_htrue_hfalse
-- name    : N4Code.dOp2_le_dO_of_htrue_hfalse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:17:23.027031+00:00
-- url     : https://prove2.me/theorems/cf1fd66a-db74-48cf-bb8e-feee8248a3c2
-- title:
--   N4 Code: d Op2 le d O of htrue hfalse
-- statement:
--   d_O' ≤ d_O when (y t₁ = true, y t₂ = false).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L261-L273
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L261-L273

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.dOp2_le_dO_of_htrue_hfalse {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n)
    (hy1 : y t₁ = true) (hy2 : y t₂ = false) :
    dOp2 C t₁ t₂ y ≤ dO C y := by sorry
