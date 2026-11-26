-- Prove2me | Theorems.Thm_N4Code_sum_Y3_weight_diff
-- name    : N4Code.sum_Y3_weight_diff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:06:54.293745+00:00
-- url     : https://prove2.me/theorems/e4711d4c-ef0f-411f-9f5a-6c7d59234b16
-- title:
--   N4 Code: sum Y3 weight diff
-- statement:
--   The Y3 part of the λ-difference, factored.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L899-L921
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L899-L921

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.sum_Y3_weight_diff {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    (∑ y ∈ Finset.univ.filter (Y3 C t),
        (weight n ε (dCode C y - 1) - weight n ε (dCode C y))) =
      (1 - ε) ^ n * (1 - ε / (1 - ε)) *
        ∑ y ∈ Finset.univ.filter (Y3 C t), (ε / (1 - ε)) ^ (dCode C y - 1) := by sorry
