-- Prove2me | Theorems.Thm_N4Code_sum_Y5_pow
-- name    : N4Code.sum_Y5_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:06:33.78066+00:00
-- url     : https://prove2.me/theorems/2807c6f8-bc93-5681-8bd2-0e3d45f63984
-- title:
--   N4 Code: sum Y5 pow
-- statement:
--   Σ over Y5 words of r^d, grouped by distance (paper `the:1` (Theorem 20)).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L850-L896
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L850-L896

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.sum_Y5_pow {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u) (r : ℝ) :
    (∑ y ∈ Finset.univ.filter (Y5 C t), r ^ (dCode C y)) =
      ∑ d ∈ Finset.Icc 1 n, (alpha5 C t (d - 1) : ℝ) * r ^ (d - 1) := by sorry
