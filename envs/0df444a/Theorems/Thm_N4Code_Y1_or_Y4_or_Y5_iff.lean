-- Prove2me | Theorems.Thm_N4Code_Y1_or_Y4_or_Y5_iff
-- name    : N4Code.Y1_or_Y4_or_Y5_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:04:53.333159+00:00
-- url     : https://prove2.me/theorems/9c8320fd-dbba-5bb5-9db4-baf6dd79356e
-- title:
--   N4 Code: Y1 or Y4 or Y5 iff
-- statement:
--   Y1 ∪ Y4 ∪ Y5 = {y : d_O ≤ d_P ∧ d_P'} (paper eq. lemma5a).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L340-L373
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L340-L373

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.Y1_or_Y4_or_Y5_iff {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    (Y1 C t y ∨ Y4 C t y ∨ Y5 C t y) ↔ dO C y ≤ min (dP C y) (dPp C t y) := by sorry
