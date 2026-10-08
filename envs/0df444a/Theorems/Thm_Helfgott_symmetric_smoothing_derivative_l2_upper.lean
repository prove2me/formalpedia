-- Prove2me | Theorems.Thm_Helfgott_symmetric_smoothing_derivative_l2_upper
-- name    : Helfgott.symmetric_smoothing_derivative_l2_upper
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-04T21:07:26.094039+00:00
-- url     : https://prove2.me/theorems/7be1a7e0-05d9-4ff5-ac25-88243f3f2fb6
-- title:
--   Elementary derivative-energy bound for the symmetric smoothing
-- statement:
--   The squared derivative energy of the symmetric smoothing, in centered coordinates on [−1,1], is at most 17/5. The formal statement displays the exact derivative expression. This rational upper bound is derived here by replacing exp(−t²) by 1 and integrating the remaining polynomial exactly. It is weaker than the numerical value in Helfgott’s paper, but sufficient with the sharper polarization estimate for the autocorrelation error.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748v2, equations (4.3), (4.5) and (7.6), https://arxiv.org/html/1312.7748v2 . The rational bound 17/5 is derived here. Written by Codex.

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open MeasureTheory
open scoped Interval

namespace Helfgott

theorem symmetric_smoothing_derivative_l2_upper :
    (∫ t in (-1 : ℝ)..1,
      (-t * (1-t^2)^2 * (7-t^2) * Real.exp (-(t^2)/2))^2) ≤ (17/5 : ℝ) := by sorry

end Helfgott
