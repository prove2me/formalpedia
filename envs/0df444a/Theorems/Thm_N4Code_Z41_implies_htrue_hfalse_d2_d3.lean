-- Prove2me | Theorems.Thm_N4Code_Z41_implies_htrue_hfalse_d2_d3
-- name    : N4Code.Z41_implies_htrue_hfalse_d2_d3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:18:38.246076+00:00
-- url     : https://prove2.me/theorems/d90d1cc0-6f6a-4abc-bca5-3b18c2985b10
-- title:
--   N4 Code: Z41 implies htrue hfalse d2 d3
-- statement:
--   y ∈ Z4¹ forces the (t,f) orientation, d₂ = d₃+1, and d₃ ≤ min(d₁,d₄)
--   (paper eq. (y41) rewrite).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1006-L1067
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1006-L1067

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.Z41_implies_htrue_hfalse_d2_d3 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) {y : Word n} (hy : Z41 C t₁ t₂ y) :
    y t₁ = true ∧ y t₂ = false ∧ dRow C 1 y = dRow C 2 y + 1 ∧
      dRow C 2 y ≤ min (dRow C 0 y) (dRow C 3 y) := by sorry
