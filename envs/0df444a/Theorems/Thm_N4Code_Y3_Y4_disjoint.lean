-- Prove2me | Theorems.Thm_N4Code_Y3_Y4_disjoint
-- name    : N4Code.Y3_Y4_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:05:36.343799+00:00
-- url     : https://prove2.me/theorems/fdf5ad1a-ef4a-4ed6-8caa-264c1d95998f
-- title:
--   N4 Code: Y3 Y4 disjoint
-- statement:
--   The N4 Code construction uses the Y3 Y4 disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L717-L722
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L717-L722

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.Y3_Y4_disjoint {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (Y3 C t y ∧ Y4 C t y) := by sorry
