-- Prove2me | Theorems.Thm_N4Code_dRow_replace_27_eq
-- name    : N4Code.dRow_replace_27_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:20:15.90881+00:00
-- url     : https://prove2.me/theorems/d153766b-a3ee-5e60-9b55-3a9a0b957a04
-- title:
--   N4 Code: d Row replace 27 eq
-- statement:
--   Replacing the two columns changes only row 2 (j ≠ 2 unchanged).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L309-L330
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L309-L330

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.dRow_replace_27_eq {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (j : Fin 4) (hj : j ≠ 2) (y : Word n) (h1 : C t₁ = col1) (h7 : C t₂ = col7) :
    dRow (replaceColumn (replaceColumn C t₁ col3) t₂ col5) j y = dRow C j y := by sorry
