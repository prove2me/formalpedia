-- Prove2me | Theorems.Thm_N4Code_Y2_or_Y3_iff
-- name    : N4Code.Y2_or_Y3_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:05:30.20413+00:00
-- url     : https://prove2.me/theorems/306a2b4d-4c2f-437b-8ccc-ca832e772cd2
-- title:
--   N4 Code: Y2 or Y3 iff
-- statement:
--   Y2 ∪ Y3 = {y : d_O > d_P ∧ d_P'}.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L376-L418
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L376-L418

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.Y2_or_Y3_iff {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    (Y2 C t y ∨ Y3 C t y) ↔ dO C y > min (dP C y) (dPp C t y) := by sorry
