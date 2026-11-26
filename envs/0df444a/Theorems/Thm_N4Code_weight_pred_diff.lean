-- Prove2me | Theorems.Thm_N4Code_weight_pred_diff
-- name    : N4Code.weight_pred_diff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:05:07.008804+00:00
-- url     : https://prove2.me/theorems/005513c8-419c-4624-8cb8-f751d3bfea50
-- title:
--   N4 Code: weight pred diff
-- statement:
--   The weight difference when the distance decreases by one (paper `the:1` (Theorem 20)).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L621-L658
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L621-L658

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.weight_pred_diff {n : ℕ} {ε : ℝ} (_hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {d : ℕ} (hd : 1 ≤ d) (hdn : d ≤ n) :
    weight n ε (d - 1) - weight n ε d =
      (1 - ε) ^ n * (1 - ε / (1 - ε)) * (ε / (1 - ε)) ^ (d - 1) := by sorry
