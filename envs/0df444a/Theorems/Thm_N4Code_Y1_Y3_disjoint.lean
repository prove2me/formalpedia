-- Prove2me | Theorems.Thm_N4Code_Y1_Y3_disjoint
-- name    : N4Code.Y1_Y3_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:07:26.65709+00:00
-- url     : https://prove2.me/theorems/ec593950-e1b4-54a0-a512-6c5ea6805977
-- title:
--   N4 Code: Y1 Y3 disjoint
-- statement:
--   The N4 Code construction uses the Y1 Y3 disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L687-L695
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L687-L695

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.Y1_Y3_disjoint {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (Y1 C t y ∧ Y3 C t y) := by sorry
