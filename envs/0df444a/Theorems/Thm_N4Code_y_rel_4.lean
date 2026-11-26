-- Prove2me | Theorems.Thm_N4Code_y_rel_4
-- name    : N4Code.y_rel_4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:04:53.619003+00:00
-- url     : https://prove2.me/theorems/66d9be0a-e02e-5128-ac81-249fc0f5b40b
-- title:
--   N4 Code: y rel 4
-- statement:
--   Lemma `lemma:1` (Lemma 19) (4): y ∈ Y4 → d_C(y) = d_O = d_C'(F1 y) = d_P.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L286-L312
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L286-L312

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.y_rel_4 {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    {y : Word n} (hy : Y4 C t y) :
    dCode C y = dO C y ∧ dCode C y = dCode C' (flipBit t y) ∧
      dCode C' (flipBit t y) = dP C y := by sorry
