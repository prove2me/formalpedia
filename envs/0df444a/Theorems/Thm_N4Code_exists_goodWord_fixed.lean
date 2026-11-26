-- Prove2me | Theorems.Thm_N4Code_exists_goodWord_fixed
-- name    : N4Code.exists_goodWord_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:19:44.942853+00:00
-- url     : https://prove2.me/theorems/bdda6f1f-f906-405f-be71-d420e8a30d58
-- title:
--   N4 Code: exists good Word fixed
-- statement:
--   A word with prescribed per-type weights and the fixed bits y t₁ = true,
--   y t₂ = false, where t₁ is a type-1 and t₂ a type-7 column.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1119-L1263
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1119-L1263

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.exists_goodWord_fixed {n : ℕ} (C : Code n) (k : ℕ → ℕ) (t₁ t₂ : Fin n)
    (ht1 : colVal (C t₁) = 1) (ht2 : colVal (C t₂) = 7)
    (hk1 : 1 ≤ k 1) (hk7 : k 7 + 1 ≤ count C 7)
    (hk : ∀ i ∈ Finset.Icc 0 15, k i ≤ count C i) :
    ∃ y : Word n, y t₁ = true ∧ y t₂ = false ∧ ∀ i ∈ Finset.Icc 0 15, w_i C i y = k i := by sorry
