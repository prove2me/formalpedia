-- Prove2me | Theorems.Thm_N4Code_Z41_of_w
-- name    : N4Code.Z41_of_w
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:21:26.43925+00:00
-- url     : https://prove2.me/theorems/5ca3db42-221d-4466-97a0-dfe17aef2172
-- title:
--   N4 Code: Z41 of w
-- statement:
--   The w-form of Z4¹ (paper eq. 2cw1-2cw3, published (204)-(206)): y₁=1, y₂=0 and the three
--   weight conditions imply y ∈ Z4¹.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1423-L1453
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1423-L1453

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.Z41_of_w {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (h07 : Columns07 C) (y : Word n)
    (hy1 : y t₁ = true) (hy2 : y t₂ = false)
    (h1eq : 2 * (w_i C 2 y + w_i C 3 y) + count C 4 + count C 5 =
        2 * (w_i C 4 y + w_i C 5 y) + count C 2 + count C 3 + 1)
    (h2ge : count C 2 + count C 3 + count C 6 + count C 7 ≤
        2 * (w_i C 2 y + w_i C 3 y + w_i C 6 y + w_i C 7 y))
    (h3ge : 2 * (w_i C 2 y + w_i C 6 y) + count C 1 + count C 5 ≥
        2 * (w_i C 1 y + w_i C 5 y) + count C 2 + count C 6) :
    Z41 C t₁ t₂ y := by sorry
