-- Prove2me | Theorems.Thm_N4Code_weight_succ_diff
-- name    : N4Code.weight_succ_diff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:06:00.859815+00:00
-- url     : https://prove2.me/theorems/c1092ae4-09bd-48a0-af02-f1acd96f36d6
-- title:
--   N4 Code: weight succ diff
-- statement:
--   The weight difference when the distance increases by one (paper `the:1` (Theorem 20)).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L661-L668
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L661-L668

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.weight_succ_diff {n : ℕ} {ε : ℝ} (_hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {d : ℕ} (hdn : d < n) :
    weight n ε (d + 1) - weight n ε d =
      -((1 - ε) ^ n * (1 - ε / (1 - ε)) * (ε / (1 - ε)) ^ d) := by sorry
