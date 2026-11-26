-- Prove2me | Theorems.Thm_N4Code_y_rel_2
-- name    : N4Code.y_rel_2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:04:44.344839+00:00
-- url     : https://prove2.me/theorems/bcd85acb-ffa6-5252-99cf-ec9cfa823581
-- title:
--   N4 Code: y rel 2
-- statement:
--   Lemma `lemma:1` (Lemma 19) (2): y ∈ Y2 → d_C(y) = d_C'(F1 y) = d_P.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L241-L261
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L241-L261

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.y_rel_2 {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    {y : Word n} (hy : Y2 C t y) :
    dCode C y = dCode C' (flipBit t y) ∧ dCode C y = dP C y := by sorry
