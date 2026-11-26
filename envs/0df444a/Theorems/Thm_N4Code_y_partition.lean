-- Prove2me | Theorems.Thm_N4Code_y_partition
-- name    : N4Code.y_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:07:46.214992+00:00
-- url     : https://prove2.me/theorems/eee9f8ab-0cf7-4157-9db1-e0e269ad8f46
-- title:
--   N4 Code: y partition
-- statement:
--   Lemma `lemma:1` (Lemma 19): Y1..Y5 form a partition of the word space.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L459-L538
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L459-L538

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.y_partition {n : ℕ} (C _C' : Code n) (t : Fin n) :
    ∀ y : Word n, ∃! i : Fin 5, YSet C t i y := by sorry
