-- Prove2me | Theorems.Thm_N4Code_y_mem
-- name    : N4Code.y_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:05:14.203952+00:00
-- url     : https://prove2.me/theorems/9547d142-1fd5-5f15-b3d6-1b1de882b934
-- title:
--   N4 Code: y mem
-- statement:
--   Exhaustiveness of the Y-partition: every word lies in some Y_i.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L732-L743
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L732-L743

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.y_mem {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    Y1 C t y ∨ Y2 C t y ∨ Y3 C t y ∨ Y4 C t y ∨ Y5 C t y := by sorry
