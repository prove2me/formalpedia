-- Prove2me | Theorems.Thm_N4Code_replace_1_3_eq
-- name    : N4Code.replace_1_3_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:03:05.875946+00:00
-- url     : https://prove2.me/theorems/b0830370-0a12-4cea-aecd-ffbc73633dda
-- title:
--   N4 Code: replace 1 3 eq
-- statement:
--   C' is exactly the replacement of column t by type 3.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L211-L215
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L211-L215

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.replace_1_3_eq {n : ℕ} (C C' : Code n) (t : Fin n) (hcol' : C' t = col3)
    (hsame : ∀ u : Fin n, u ≠ t → C' u = C u) :
    C' = replaceColumn C t col3 := by sorry
