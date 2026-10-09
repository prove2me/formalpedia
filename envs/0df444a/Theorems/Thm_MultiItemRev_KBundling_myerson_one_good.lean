-- Prove2me | Theorems.Thm_MultiItemRev_KBundling_myerson_one_good
-- name    : MultiItemRev.KBundling.myerson_one_good
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:11:51.100185+00:00
-- url     : https://prove2.me/theorems/1c5159cd-4b31-4172-a505-5ffa751fac15
-- title:
--   (1), p. 12 — one good: Rev(X) = sup_{p≥0} p·P[X ≥ p] = sup p·P[X > p] = sup p·(1 − F(p))
-- statement:
--   Myerson's characterization of the optimal revenue from one good.
--
--   Let $X$ be a one-good random valuation, i.e. a nonnegative random variable with law $\nu$ and distribution function $F(p)=\mathbb P[X\le p]$. Then
--   $$\mathrm{Rev}(X)=\sup_{p\ge0}p\cdot\mathbb P[X\ge p]=\sup_{p\ge0}p\cdot\mathbb P[X>p]=\sup_{p\ge0}p\cdot(1-F(p)).$$
--
--   The optimal one-good mechanism is thus a posted price. Every one-good comparison in the paper (monotonicity, the ER law, separate and bundled revenues) goes through this formula.
--
--   **Formalization Note** All three suprema are in $[0,\infty]$, matching $\mathrm{Rev}$; $1-F(p)$ is `1 - ν {t | t ≤ p}` in `ℝ≥0∞`. The same statement is posed in the sibling missions 2 and 3 of this series.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 12, display (1) (Myerson 1981)

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.KBundling

theorem myerson_one_good (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] :
    MultiItemRev.Decomp.Rev1 ν = ⨆ p : ℝ≥0, (p : ℝ≥0∞) * ν {t | p ≤ t} ∧
    MultiItemRev.Decomp.Rev1 ν = ⨆ p : ℝ≥0, (p : ℝ≥0∞) * ν {t | p < t} ∧
    MultiItemRev.Decomp.Rev1 ν = ⨆ p : ℝ≥0, (p : ℝ≥0∞) * (1 - ν {t | t ≤ p}) := by sorry

end MultiItemRev.KBundling
