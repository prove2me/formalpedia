-- Prove2me | Theorems.Thm_N4Code_dOp2_eq_min_of_htrue_hfalse
-- name    : N4Code.dOp2_eq_min_of_htrue_hfalse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:17:51.891874+00:00
-- url     : https://prove2.me/theorems/65a6823c-613c-557e-a8cf-da95cb672a58
-- title:
--   N4 Code: d Op2 eq min of htrue hfalse
-- statement:
--   d_O' = min(d₁, d₂−2, d₄) in the (t,f) orientation.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L961-L973
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L961-L973

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.dOp2_eq_min_of_htrue_hfalse {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n)
    (hy1 : y t₁ = true) (hy2 : y t₂ = false) :
    dOp2 C t₁ t₂ y = min (dRow C 0 y) (min (dRow C 1 y - 2) (dRow C 3 y)) := by sorry
