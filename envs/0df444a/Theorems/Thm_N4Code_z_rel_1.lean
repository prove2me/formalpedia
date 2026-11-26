-- Prove2me | Theorems.Thm_N4Code_z_rel_1
-- name    : N4Code.z_rel_1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:20:45.781252+00:00
-- url     : https://prove2.me/theorems/28b70463-1654-5330-a6b6-326a860d898e
-- title:
--   N4 Code: z rel 1
-- statement:
--   Lemma `lemma:2` (Lemma 22) (1): y ∈ Z1 → d_C(y) = d_C'(y).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L751-L762
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L751-L762

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.z_rel_1 {n : ℕ} (C C' : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7)
    (h3 : C' t₁ = col3) (h5 : C' t₂ = col5)
    (hsame : ∀ u : Fin n, u ≠ t₁ → u ≠ t₂ → C' u = C u) {y : Word n}
    (hy : Z1 C t₁ t₂ y) : dCode C y = dCode C' y := by sorry
