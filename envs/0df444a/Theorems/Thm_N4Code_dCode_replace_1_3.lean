-- Prove2me | Theorems.Thm_N4Code_dCode_replace_1_3
-- name    : N4Code.dCode_replace_1_3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:03:05.281853+00:00
-- url     : https://prove2.me/theorems/8eec77e5-c0d5-572d-ab21-d1e02213d712
-- title:
--   N4 Code: d Code replace 1 3
-- statement:
--   d_{C'}(y) = min(d_O(y), d_P'(y)) for the one-column change (paper eq. dcp).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L188-L201
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L188-L201

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.dCode_replace_1_3 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) (hcol : C t = col1) :
    dCode (replaceColumn C t col3) y = min (dO C y) (dPp C t y) := by sorry
