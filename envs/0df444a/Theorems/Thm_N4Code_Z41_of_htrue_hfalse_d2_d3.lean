-- Prove2me | Theorems.Thm_N4Code_Z41_of_htrue_hfalse_d2_d3
-- name    : N4Code.Z41_of_htrue_hfalse_d2_d3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:21:26.624958+00:00
-- url     : https://prove2.me/theorems/894e4ec7-ac09-4135-a436-1b6519bb2483
-- title:
--   N4 Code: Z41 of htrue hfalse d2 d3
-- statement:
--   y with y₁=1, y₂=0, d₂ = d₃+1, d₃ ≤ min(d₁,d₄) lies in Z4¹
--   (the converse of `Z41_implies_htrue_hfalse_d2_d3`).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1310-L1371
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1310-L1371

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.Z41_of_htrue_hfalse_d2_d3 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) {y : Word n}
    (hy1 : y t₁ = true) (hy2 : y t₂ = false)
    (hd2 : dRow C 1 y = dRow C 2 y + 1)
    (hd3 : dRow C 2 y ≤ min (dRow C 0 y) (dRow C 3 y)) :
    Z41 C t₁ t₂ y := by sorry
