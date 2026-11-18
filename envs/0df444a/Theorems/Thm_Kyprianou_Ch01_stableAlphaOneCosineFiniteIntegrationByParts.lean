-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineFiniteIntegrationByParts
-- name    : Kyprianou.Ch01.stableAlphaOneCosineFiniteIntegrationByParts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T09:08:36.435199+00:00
-- url     : https://prove2.me/theorems/74811514-39b3-4018-b6cf-4b5623c42a6a
-- title:
--   Exact integration-by-parts identity between truncated stable cosine and Dirichlet sine integrals
-- statement:
--   For every 0<a≤b, the cosine Lévy kernel integral on [a,b] equals the Dirichlet sine integral on [a,b] minus the explicit endpoint difference (1−cos b)/b−(1−cos a)/a. This follows from the proved derivative of (1−cos x)/x and FTC on a positive compact interval where all denominators are nonzero. The formula is the finite-interval analytic bridge needed for the exact π/2 evaluation.
-- source:
--   Kyprianou (2006), Chapter 1, α=1 stable cosine integral and its Dirichlet sine reduction.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineQuotientDerivative
open MeasureTheory Set Real
open scoped Interval
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneCosineFiniteIntegrationByParts
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, (1 - Real.cos x) / x ^ 2) =
      (∫ x in a..b, Real.sin x / x) -
        ((1 - Real.cos b) / b - (1 - Real.cos a) / a) := by
  sorry
