-- Prove2me | Theorems.Thm_N4Code_dP_add_two_of_hfalse_htrue
-- name    : N4Code.dP_add_two_of_hfalse_htrue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:18:31.498928+00:00
-- url     : https://prove2.me/theorems/1727682d-dfae-5018-aafc-ae1c47c86d88
-- title:
--   N4 Code: d P add two of hfalse htrue
-- statement:
--   d_P + 2 = d_P' when (y t₁ = false, y t₂ = true).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L299-L304
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L299-L304

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.dP_add_two_of_hfalse_htrue {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n)
    (hy1 : y t₁ = false) (hy2 : y t₂ = true) :
    dP C y + 2 = dPp2 C t₁ t₂ y := by sorry
