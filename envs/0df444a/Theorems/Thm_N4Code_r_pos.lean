-- Prove2me | Theorems.Thm_N4Code_r_pos
-- name    : N4Code.r_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:04:39.161205+00:00
-- url     : https://prove2.me/theorems/8d1ba536-c266-5216-b2ce-3c94ba390e9d
-- title:
--   N4 Code: r pos
-- statement:
--   r = ε/(1−ε) is positive for 0 < ε < 1/2.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L1285-L1287
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L1285-L1287

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.r_pos {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) : 0 < ε / (1 - ε) := by sorry
