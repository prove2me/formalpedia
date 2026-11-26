-- Prove2me | Theorems.Thm_N4Code_Z5_of_w
-- name    : N4Code.Z5_of_w
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:21:44.778763+00:00
-- url     : https://prove2.me/theorems/d8008bb7-b998-4f80-8021-b10f9de4391c
-- title:
--   N4 Code: Z5 of w
-- statement:
--   The w-form of Z5 (paper eq. 3cw2/4cw2 and 3cw3/4cw3, published
--   (208)-(210) for the odd case, (211)-(213) for the even case): y₁=1, y₂=0,
--   d₁ + c = d₃ (c ∈ {0,1}), and the two weight inequalities imply y ∈ Z5.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1681-L1757
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1681-L1757

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.Z5_of_w {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (h07 : Columns07 C) (y : Word n)
    (hy1 : y t₁ = true) (hy2 : y t₂ = false)
    (c : ℕ) (hc : c ≤ 1) (hd12c : dRow C 1 y + c = dRow C 2 y)
    (h2ge : count C 2 + count C 3 + count C 6 + count C 7 - 1 ≤
        2 * (w_i C 2 y + w_i C 3 y + w_i C 6 y + w_i C 7 y))
    (h3le : 2 * (w_i C 1 y + w_i C 5 y) + count C 2 + count C 6 ≤
        2 * (w_i C 2 y + w_i C 6 y) + count C 1 + count C 5 + 1) :
    Z5 C t₁ t₂ y := by sorry
