-- Prove2me | Theorems.Thm_N4Code_sum_sub_two_pos
-- name    : N4Code.sum_sub_two_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:19:22.522095+00:00
-- url     : https://prove2.me/theorems/b516c806-e68b-5b04-be07-480e80f6b2c3
-- title:
--   N4 Code: sum sub two pos
-- statement:
--   If two functions agree off {t₁,t₂} and the first is one larger at both
--   positions, the first sum is two larger.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L45-L78
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L45-L78

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.sum_sub_two_pos {n : ℕ} (f g : Fin n → ℕ) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : f t₁ = g t₁ + 1) (h2 : f t₂ = g t₂ + 1)
    (hrest : ∀ u : Fin n, u ≠ t₁ → u ≠ t₂ → f u = g u) :
    (∑ u : Fin n, f u) = (∑ u : Fin n, g u) + 2 := by sorry
