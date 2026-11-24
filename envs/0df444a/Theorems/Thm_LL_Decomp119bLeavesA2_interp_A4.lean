-- Prove2me | Theorems.Thm_LL_Decomp119bLeavesA2_interp_A4
-- name    : LL_Decomp119bLeavesA2.interp_A4
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-24T15:48:55.256683+00:00
-- url     : https://prove2.me/theorems/2c687137-cc8b-42bf-87db-a3b148b16376
-- title:
--   Interpolation inequality A.4 for $C^2$ functions
-- statement:
--   Let $g:\mathbb R\to\mathbb C$ be twice continuously differentiable, $a\le b$, and suppose $\|g''(v)\|\le M$ for all $v\in[a,b]$. Then for every $t\in[a,b]$, $\|g(t)\|\le\max(\|g(a)\|,\|g(b)\|)+\frac{(b-a)^2}{8}M$.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach's problem, arXiv:1205.5252, Lemma A.2, pages 74 and 75

import Mathlib

open MeasureTheory Set Real

namespace LL_Decomp119bLeavesA2
theorem interp_A4 (g : ℝ → ℂ) (M a b : ℝ) (hab : a ≤ b) (hg : ContDiff ℝ 2 g)
    (hM : ∀ v ∈ Icc a b, ‖deriv (deriv g) v‖ ≤ M) (t : ℝ) (ht : t ∈ Icc a b) :
    ‖g t‖ ≤ max ‖g a‖ ‖g b‖ + (b - a) ^ 2 / 8 * M := by sorry
end LL_Decomp119bLeavesA2
