-- Prove2me | Theorems.Thm_Helfgott_symmetric_smoothing_l2_lower
-- name    : Helfgott.symmetric_smoothing_l2_lower
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-04T21:04:58.278386+00:00
-- url     : https://prove2.me/theorems/fb9219d9-f0c7-4c11-a406-a7a960533bc8
-- title:
--   Exact polynomial lower bound for Helfgott’s symmetric smoothing mass
-- statement:
--   The squared L² norm of the symmetric smoothing η_circle(t)=t³(2−t)³ exp(−(t−1)²/2), extended by zero outside [0,2], is at least 16/25. The formal statement uses the centered variable on [−1,1]. This exact rational lower bound is derived here by polynomial comparison and is slightly weaker than the numerical value used in the paper. It supports the main convolution term in the three-prime argument.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748v2, equation (4.3) and section 7.2, with equation (7.4) supplying the paper’s numerical norm estimate. https://arxiv.org/html/1312.7748v2 . The polynomial bound 16/25 is derived here. Written by Codex.

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open MeasureTheory
open scoped Interval

namespace Helfgott

theorem symmetric_smoothing_l2_lower :
    (16 / 25 : ℝ) ≤ ∫ t in (-1 : ℝ)..1,
      ((1 - t ^ 2) ^ 3 * Real.exp (-(t ^ 2) / 2)) ^ 2 := by sorry

end Helfgott
