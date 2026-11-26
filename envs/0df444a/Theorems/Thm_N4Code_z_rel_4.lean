-- Prove2me | Theorems.Thm_N4Code_z_rel_4
-- name    : N4Code.z_rel_4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:20:49.666277+00:00
-- url     : https://prove2.me/theorems/15ca1618-b6df-5f88-90be-4aad0f5f1286
-- title:
--   N4 Code: z rel 4
-- statement:
--   Lemma `lemma:2` (Lemma 22) (4): y ∈ Z4 → d_C(y) = min(d_O,d_P) ∧ d_P ≥ d_C'(F2 y) = d_O'.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L802-L828
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L802-L828

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.z_rel_4 {n : ℕ} (C C' : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7)
    (h3 : C' t₁ = col3) (h5 : C' t₂ = col5)
    (hsame : ∀ u : Fin n, u ≠ t₁ → u ≠ t₂ → C' u = C u) {y : Word n}
    (hy : Z4 C t₁ t₂ y) :
    dCode C y = min (dO C y) (dP C y) ∧
      dCode C' (flipTwoBits t₁ t₂ y) = dOp2 C t₁ t₂ y ∧
        dP C y ≥ dCode C' (flipTwoBits t₁ t₂ y) := by sorry
