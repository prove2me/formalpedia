-- Prove2me | Theorems.Thm_NullConeGravity_gaussian_area_window_normalization
-- name    : NullConeGravity.gaussian_area_window_normalization
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T20:37:02.310034+00:00
-- url     : https://prove2.me/theorems/b93f54f1-7446-4139-86db-f5d08920bee7
-- title:
--   Gaussian area-window normalization (Eq. 5.66)
-- statement:
--   Fix a nonnegative dimensionless area eigenvalue $s$. Let $t=s_b>0$ be the center of the Gaussian area window and take its variance to be $2t$, as in Eqs. (5.25) and (5.66). The window integrates to one over its centers.
--
--   $$\int_0^\infty \frac{\exp\!\left(-\frac{(s-t)^2}{4t}\right)}{\sqrt{4\pi t}}\,dt=1.$$
--
--   This is the first equality of Eq. (5.66), including the eigenvalue $s=0$.
-- source:
--   Venkatesa Chandrasekaran, An algebraic quantization of gravity from the null cone, arXiv:2611.34924v1, §5.3, first equality of Eq. (5.66), using the window in Eq. (5.25). https://arxiv.org/html/2611.34924v1#S5.E66

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open Set MeasureTheory

namespace NullConeGravity
theorem gaussian_area_window_normalization (s : ℝ) (hs : 0 ≤ s) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-((s - t) ^ 2) / (4 * t)) / Real.sqrt (4 * Real.pi * t)) = 1 := by sorry
end NullConeGravity
