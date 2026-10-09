-- Prove2me | Theorems.Thm_MultiItemRev_TwoIID_myerson_one_good
-- name    : MultiItemRev.TwoIID.myerson_one_good
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:29:43.115034+00:00
-- url     : https://prove2.me/theorems/04e26d8e-1b2b-4bea-9a1f-ace2d6649bbe
-- title:
--   Equation (1), p. 12 — one-good posted-price revenue
-- statement:
--   Let $X$ be a nonnegative one-good valuation with an arbitrary probability law. Its optimal revenue equals the supremum of posted-price revenue whether a buyer at the price is included or excluded:
--
--   $$\operatorname{Rev}_1(X)=\sup_{p\ge0}p\Pr[X\ge p]=\sup_{p\ge0}p\Pr[X>p].$$
--
--   The second probability is $1-F(p)$ for the cumulative distribution function $F$. This equation reduces the one-good revenue terms in Theorem B to a tail bound.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 12, equation (1), citing Myerson (1981)

import Mathlib
import Definitions.Def_MultiItemRev_TwoIID_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.TwoIID

theorem myerson_one_good (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] :
    MultiItemRev.Decomp.Rev1 ν = ⨆ p : ℝ≥0, (p : ℝ≥0∞) * ν {t | p ≤ t} ∧
    MultiItemRev.Decomp.Rev1 ν = ⨆ p : ℝ≥0, (p : ℝ≥0∞) * ν {t | p < t} := by sorry

end MultiItemRev.TwoIID
