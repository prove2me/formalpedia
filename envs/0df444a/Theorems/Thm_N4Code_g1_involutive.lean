-- Prove2me | Theorems.Thm_N4Code_g1_involutive
-- name    : N4Code.g1_involutive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:05:57.970856+00:00
-- url     : https://prove2.me/theorems/ce0be832-fe9c-4f44-bc30-4f7180551e35
-- title:
--   N4 Code: g1 involutive
-- statement:
--   g1 is an involution.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L589-L594
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L589-L594

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.g1_involutive {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    g1 C t (g1 C t y) = y := by sorry
