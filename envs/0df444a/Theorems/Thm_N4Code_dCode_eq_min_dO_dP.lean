-- Prove2me | Theorems.Thm_N4Code_dCode_eq_min_dO_dP
-- name    : N4Code.dCode_eq_min_dO_dP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:03:02.516168+00:00
-- url     : https://prove2.me/theorems/49a90fbb-e580-4608-b624-67c55efc9ed8
-- title:
--   N4 Code: d Code eq min d O d P
-- statement:
--   d_C(y) = min(d_O(y), d_P(y)) (paper eq. dc).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L162-L165
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L162-L165

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.dCode_eq_min_dO_dP {n : ℕ} (C : Code n) (y : Word n) :
    dCode C y = min (dO C y) (dP C y) := by sorry
