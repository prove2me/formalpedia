-- Prove2me | Theorems.Thm_N4Code_Y4_Y5_disjoint
-- name    : N4Code.Y4_Y5_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:05:51.106135+00:00
-- url     : https://prove2.me/theorems/0efc0b3c-96dc-420a-80e8-e77d631020b6
-- title:
--   N4 Code: Y4 Y5 disjoint
-- statement:
--   The N4 Code construction uses the Y4 Y5 disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L440-L446
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L440-L446

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.Y4_Y5_disjoint {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (Y4 C t y ∧ Y5 C t y) := by sorry
