-- Prove2me | Theorems.Thm_MultiItemRev_KSeparate_myerson_one_good
-- name    : MultiItemRev.KSeparate.myerson_one_good
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:28:46.374772+00:00
-- url     : https://prove2.me/theorems/49a9ba5a-2228-4d2d-a941-b27283bfe883
-- title:
--   (1), p. 12 — one-good revenue equals the best posted-price revenue
-- statement:
--   Let $X$ be a nonnegative one-good valuation with probability law $\nu$, and let $F(p)=\Pr[X\le p]$. Its optimal incentive-compatible, individually rational revenue satisfies all three equivalent posted-price formulas:
--
--   $$\operatorname{Rev}(X)=\sup_{p\ge0}p\Pr[X\ge p]=\sup_{p\ge0}p\Pr[X>p]=\sup_{p\ge0}p(1-F(p)).$$
--
--   This characterizes one-good revenue through tail probabilities and underlies the monotonicity and equal-revenue comparisons.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 12, display (1)

import Mathlib
import Definitions.Def_MultiItemRev_KSeparate_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.KSeparate

theorem myerson_one_good (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] :
    MultiItemRev.Decomp.Rev1 ν = ⨆ p : ℝ≥0, (p : ℝ≥0∞) * ν {t | p ≤ t} ∧
    MultiItemRev.Decomp.Rev1 ν = ⨆ p : ℝ≥0, (p : ℝ≥0∞) * ν {t | p < t} ∧
    MultiItemRev.Decomp.Rev1 ν = ⨆ p : ℝ≥0, (p : ℝ≥0∞) * (1 - ν {t | t ≤ p}) := by sorry

end MultiItemRev.KSeparate
