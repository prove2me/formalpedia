-- Prove2me | Theorems.Thm_N4Code_Y2_Y3_disjoint
-- name    : N4Code.Y2_Y3_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:04:24.733749+00:00
-- url     : https://prove2.me/theorems/05c4e49a-5f43-586c-abf0-7cc81b094971
-- title:
--   N4 Code: Y2 Y3 disjoint
-- statement:
--   The N4 Code construction uses the Y2 Y3 disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L448-L456
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L448-L456

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.Y2_Y3_disjoint {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (Y2 C t y ∧ Y3 C t y) := by sorry
