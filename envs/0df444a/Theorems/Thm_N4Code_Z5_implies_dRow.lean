-- Prove2me | Theorems.Thm_N4Code_Z5_implies_dRow
-- name    : N4Code.Z5_implies_dRow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:18:11.275385+00:00
-- url     : https://prove2.me/theorems/90733ea0-839f-4c21-9055-0faae90641fc
-- title:
--   N4 Code: Z5 implies d Row
-- statement:
--   y ∈ Z5 forces the (t,f) orientation and the dRow conditions
--   d₁ ≤ d₃, d₃−1 ≤ d₀, d₃−1 ≤ d₄ (paper rewrite of eq. y25).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2238-L2294
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2238-L2294

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.Z5_implies_dRow {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) {y : Word n} (hy : Z5 C t₁ t₂ y) :
    y t₁ = true ∧ y t₂ = false ∧ dRow C 1 y ≤ dRow C 2 y ∧
      dRow C 2 y - 1 ≤ dRow C 0 y ∧ dRow C 2 y - 1 ≤ dRow C 3 y ∧
        dRow C 2 y - 1 ≤ dO C y := by sorry
