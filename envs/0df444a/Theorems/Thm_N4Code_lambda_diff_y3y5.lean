-- Prove2me | Theorems.Thm_N4Code_lambda_diff_y3y5
-- name    : N4Code.lambda_diff_y3y5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:06:39.505976+00:00
-- url     : https://prove2.me/theorems/f3bb59f0-861a-531a-bfab-748e854b3db9
-- title:
--   N4 Code: lambda diff y3y5
-- statement:
--   λ_{C'} − λ_C equals a weighted sum over Y3 (closer) and Y5 (farther) only.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L950-L1046
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L950-L1046

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.lambda_diff_y3y5 {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u) (ε : ℝ) :
    lambda C' ε - lambda C ε =
      (1 / 4 : ℝ) *
        ((∑ y ∈ Finset.univ.filter (Y3 C t),
            (weight n ε (dCode C y - 1) - weight n ε (dCode C y))) +
         (∑ y ∈ Finset.univ.filter (Y5 C t),
            (weight n ε (dCode C y + 1) - weight n ε (dCode C y)))) := by sorry
