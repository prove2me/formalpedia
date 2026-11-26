-- Prove2me | Theorems.Thm_N4Code_sum_Y5_weight_diff
-- name    : N4Code.sum_Y5_weight_diff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:06:41.882688+00:00
-- url     : https://prove2.me/theorems/817b8983-2f45-42c5-81ba-d00b1ad6434c
-- title:
--   N4 Code: sum Y5 weight diff
-- statement:
--   The Y5 part of the λ-difference, factored.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L924-L947
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L924-L947

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.sum_Y5_weight_diff {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    (∑ y ∈ Finset.univ.filter (Y5 C t),
        (weight n ε (dCode C y + 1) - weight n ε (dCode C y))) =
      -((1 - ε) ^ n * (1 - ε / (1 - ε)) *
          ∑ y ∈ Finset.univ.filter (Y5 C t), (ε / (1 - ε)) ^ (dCode C y)) := by sorry
