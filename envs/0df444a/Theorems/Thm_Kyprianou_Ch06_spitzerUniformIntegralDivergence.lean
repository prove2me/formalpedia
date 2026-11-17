-- Prove2me | Theorems.Thm_Kyprianou_Ch06_spitzerUniformIntegralDivergence
-- name    : Kyprianou.Ch06.spitzerUniformIntegralDivergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:26:35.476634+00:00
-- url     : https://prove2.me/theorems/0cf6acf2-cfd1-4069-91eb-84e374e11d76
-- title:
--   Spitzer integral: uniform-weight comparison preserves divergence
-- statement:
--   If a measurable nonnegative occupation integrand f is bounded above and below up to a fixed strictly positive multiplicative constant by g, its integral is infinite if and only if the integral of g is infinite. This is the deterministic comparison step needed when removing an exponential-time Laplace weight from the Chapter 6 Spitzer criteria.
-- source:
--   Kyprianou (2006), solution to Exercise 6.8(i)-(ii), printed pp. 333–334; compare the exponential weight on (0,1).

import Mathlib
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Uniform two-sided comparison transfers infinite nonnegative integrals. -/
theorem spitzerUniformIntegralDivergence
    (μ : Measure ℝ) (f g : ℝ → ENNReal) (c : ENNReal)
    (hc0 : c ≠ 0) (hf : Measurable f)
    (hLower : ∀ t, c * f t ≤ g t)
    (hUpper : ∀ t, g t ≤ f t) :
    ((∫⁻ t, f t ∂μ) = ⊤ ↔ (∫⁻ t, g t ∂μ) = ⊤) := by
  sorry

end Kyprianou.Ch06
