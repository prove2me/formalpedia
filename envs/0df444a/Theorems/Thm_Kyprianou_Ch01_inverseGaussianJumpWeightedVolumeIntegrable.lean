-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianJumpWeightedVolumeIntegrable
-- name    : Kyprianou.Ch01.inverseGaussianJumpWeightedVolumeIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:08:12.495243+00:00
-- url     : https://prove2.me/theorems/87ebd12e-92d8-466b-9a26-9f3d3a365002
-- title:
--   Inverse-Gaussian complex jump kernel weighted by its true density is integrable
-- statement:
--   For b>0 and every θ, the exact original inverse-Gaussian Lévy density times the complex Fourier jump kernel 1−exp(iθx) is Bochner-integrable over x>0 with respect to Lebesgue measure. Near zero the kernel is O(x) and the density is O(x^(−3/2)), while the density is exponentially tilted at infinity. This is the exact weighted analytic obligation, enabling the original Lévy-measure integral by Mathlib withDensity transfer.
-- source:
--   Kyprianou (2006), Chapter 1 inverse-Gaussian Lévy exponent, weighted-integrability child.

import Mathlib
open MeasureTheory Set Complex ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianJumpWeightedVolumeIntegrable
    (b : ℝ) (hb : 0 < b) :
    ∀ theta : ℝ,
      Integrable
        (fun x : ℝ =>
          (ENNReal.ofReal
            ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-(b ^ 2 * x / 2)))).toReal •
            ((1 : ℂ) - Complex.exp
              (Complex.I * ((theta * x : ℝ) : ℂ))))
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
  sorry
