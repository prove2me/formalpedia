-- Prove2me | Theorems.Thm_N4Code_Y3_Y5_disjoint
-- name    : N4Code.Y3_Y5_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:06:19.907359+00:00
-- url     : https://prove2.me/theorems/c7238d8b-9139-4e12-b65c-f49aca2d7052
-- title:
--   N4 Code: Y3 Y5 disjoint
-- statement:
--   The N4 Code construction uses the Y3 Y5 disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L724-L729
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L724-L729

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.Y3_Y5_disjoint {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (Y3 C t y ∧ Y5 C t y) := by sorry
