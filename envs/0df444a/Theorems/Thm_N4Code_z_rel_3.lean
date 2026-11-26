-- Prove2me | Theorems.Thm_N4Code_z_rel_3
-- name    : N4Code.z_rel_3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:20:57.009811+00:00
-- url     : https://prove2.me/theorems/f550f388-af36-460a-8d68-89f329dc4ce7
-- title:
--   N4 Code: z rel 3
-- statement:
--   Lemma `lemma:2` (Lemma 22) (3): y ∈ Z3 → d_C(y) = d_C'(F2 y) = d_P.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L783-L799
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L783-L799

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.z_rel_3 {n : ℕ} (C C' : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7)
    (h3 : C' t₁ = col3) (h5 : C' t₂ = col5)
    (hsame : ∀ u : Fin n, u ≠ t₁ → u ≠ t₂ → C' u = C u) {y : Word n}
    (hy : Z3 C t₁ t₂ y) :
    dCode C y = dCode C' (flipTwoBits t₁ t₂ y) ∧ dCode C y = dP C y := by sorry
