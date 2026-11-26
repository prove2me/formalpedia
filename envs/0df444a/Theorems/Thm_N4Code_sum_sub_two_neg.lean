-- Prove2me | Theorems.Thm_N4Code_sum_sub_two_neg
-- name    : N4Code.sum_sub_two_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:20:07.276257+00:00
-- url     : https://prove2.me/theorems/268f970e-e3f3-45b7-a018-f4c72f2614de
-- title:
--   N4 Code: sum sub two neg
-- statement:
--   If two functions agree off {t₁,t₂} and the first is one smaller at both
--   positions, the first sum is two smaller.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L82-L92
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L82-L92

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.sum_sub_two_neg {n : ℕ} (f g : Fin n → ℕ) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : f t₁ + 1 = g t₁) (h2 : f t₂ + 1 = g t₂)
    (hrest : ∀ u : Fin n, u ≠ t₁ → u ≠ t₂ → f u = g u) :
    (∑ u : Fin n, f u) + 2 = (∑ u : Fin n, g u) := by sorry
