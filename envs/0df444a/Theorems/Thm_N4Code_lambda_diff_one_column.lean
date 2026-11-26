-- Prove2me | Theorems.Thm_N4Code_lambda_diff_one_column
-- name    : N4Code.lambda_diff_one_column
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:04:30.689231+00:00
-- url     : https://prove2.me/theorems/78d11f3c-7012-46dd-94e4-bae647d422a8
-- title:
--   N4 Code: lambda diff one column
-- statement:
--   Theorem `the:1` (Theorem 20): exact λ-difference for a one-column change.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L1049-L1074
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L1049-L1074

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.lambda_diff_one_column {n : ℕ} (C C' : Code n) (t : Fin n)
    (hcol : C t = col1) (hcol' : C' t = col3)
    (hsame : ∀ u : Fin n, u ≠ t → C' u = C u) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      lambda C' ε - lambda C ε =
        ((1 - ε) ^ n / 4) * (1 - ε / (1 - ε)) *
          ∑ d ∈ Finset.Icc 1 n,
            ((alpha3 C t d : ℝ) - (alpha5 C t (d - 1) : ℝ)) *
              (ε / (1 - ε)) ^ (d - 1) := by sorry
