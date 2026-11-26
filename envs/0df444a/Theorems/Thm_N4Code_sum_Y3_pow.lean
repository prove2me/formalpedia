-- Prove2me | Theorems.Thm_N4Code_sum_Y3_pow
-- name    : N4Code.sum_Y3_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:06:31.712011+00:00
-- url     : https://prove2.me/theorems/eeb2cb76-edce-53cb-a9a2-d1b30996c8d3
-- title:
--   N4 Code: sum Y3 pow
-- statement:
--   Σ over Y3 words of r^(d−1), grouped by distance (paper `the:1` (Theorem 20)).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L835-L847
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L835-L847

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.sum_Y3_pow {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u) (r : ℝ) :
    (∑ y ∈ Finset.univ.filter (Y3 C t), r ^ (dCode C y - 1)) =
      ∑ d ∈ Finset.Icc 1 n, (alpha3 C t d : ℝ) * r ^ (d - 1) := by sorry
