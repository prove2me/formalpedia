-- Prove2me | Theorems.Thm_N4Code_r_pow_sub_pos
-- name    : N4Code.r_pow_sub_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:05:30.211497+00:00
-- url     : https://prove2.me/theorems/a0669f56-7e32-5311-88d7-bd4b576a715d
-- title:
--   N4 Code: r pow sub pos
-- statement:
--   r^(d−1) − r^d > 0 for d ≥ 1 and 0 < ε < 1/2.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L1295-L1311
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L1295-L1311

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.r_pow_sub_pos {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) {d : ℕ} (hd : 1 ≤ d) :
    0 < (ε / (1 - ε)) ^ (d - 1) - (ε / (1 - ε)) ^ d := by sorry
