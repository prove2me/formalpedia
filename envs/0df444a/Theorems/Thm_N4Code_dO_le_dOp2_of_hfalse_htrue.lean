-- Prove2me | Theorems.Thm_N4Code_dO_le_dOp2_of_hfalse_htrue
-- name    : N4Code.dO_le_dOp2_of_hfalse_htrue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:18:27.77655+00:00
-- url     : https://prove2.me/theorems/30e78849-1c9c-5dd5-82bb-578c67be0d05
-- title:
--   N4 Code: d O le d Op2 of hfalse htrue
-- statement:
--   d_O ≤ d_O' when (y t₁ = false, y t₂ = true).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L276-L288
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L276-L288

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.dO_le_dOp2_of_hfalse_htrue {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n)
    (hy1 : y t₁ = false) (hy2 : y t₂ = true) :
    dO C y ≤ dOp2 C t₁ t₂ y := by sorry
