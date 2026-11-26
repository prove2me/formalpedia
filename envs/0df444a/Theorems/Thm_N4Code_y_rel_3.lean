-- Prove2me | Theorems.Thm_N4Code_y_rel_3
-- name    : N4Code.y_rel_3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:03:09.370726+00:00
-- url     : https://prove2.me/theorems/8c3540bd-b8cb-4afa-91d0-3686245ab273
-- title:
--   N4 Code: y rel 3
-- statement:
--   Lemma `lemma:1` (Lemma 19) (3): y ∈ Y3 → d_C(y) = d_P = d_C'(y) + 1.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L264-L283
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L264-L283

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.y_rel_3 {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    {y : Word n} (hy : Y3 C t y) :
    dCode C y = dP C y ∧ dCode C y = dCode C' y + 1 := by sorry
