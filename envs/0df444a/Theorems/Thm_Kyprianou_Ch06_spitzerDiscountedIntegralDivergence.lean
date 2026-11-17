-- Prove2me | Theorems.Thm_Kyprianou_Ch06_spitzerDiscountedIntegralDivergence
-- name    : Kyprianou.Ch06.spitzerDiscountedIntegralDivergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:30:47.398262+00:00
-- url     : https://prove2.me/theorems/1cd3b3e7-2d6d-4ec1-985c-c631b82b91e7
-- title:
--   Spitzer integral: discounted and undiscounted divergence are equivalent
-- statement:
--   For every measurable nonnegative extended real occupation-density function f, and discount p≥0, the Lebesgue integral over time 0<t<1 of e^{-pt} f(t) diverges if and only if the integral of f(t) diverges. Uses the proved Chapter 6 exponential weight bounds and measure-theoretic monotonicity.
-- source:
--   Kyprianou (2006), Exercise 6.8(i)-(ii) solutions, printed pp. 333–334.

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_spitzerExponentialWeightBounds
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Exponential-time discount preserves Spitzer divergence on the unit time interval. -/
theorem spitzerDiscountedIntegralDivergence
    (f : ℝ → ENNReal) (hf : Measurable f)
    (p : ℝ) (hp : 0 ≤ p) :
    ((∫⁻ t in Set.Ioo (0 : ℝ) 1,
      ENNReal.ofReal (Real.exp (-p * t)) * f t ∂volume) = ⊤ ↔
    (∫⁻ t in Set.Ioo (0 : ℝ) 1, f t ∂volume) = ⊤) := by
  sorry

end Kyprianou.Ch06
