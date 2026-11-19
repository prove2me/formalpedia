-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianTruncatedMomentRealIntegrable
-- name    : Kyprianou.Ch01.inverseGaussianTruncatedMomentRealIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:51:15.422011+00:00
-- url     : https://prove2.me/theorems/58a829d2-f992-4ff1-bf02-94a521778570
-- title:
--   Inverse-Gaussian Lévy density has integrable truncated quadratic real moment
-- statement:
--   For every b>0, the exact real jump-density (min(1,x²))/sqrt(2*pi*x³)*exp(-b²*x/2) is integrable with respect to Lebesgue measure on x>0. At the origin it is O(x^(1/2)), while for x>1 it is bounded by an integrable power x^(-3/2). This preserves the source jump density and is the genuinely analytic missing obligation for the inverse-Gaussian Lévy-measure proof.
-- source:
--   Kyprianou (2006) Chapter 1 inverse-Gaussian Lévy density; exact integrability child of inverseGaussianLevyMeasureTruncatedMomentFinite.

import Mathlib
open MeasureTheory Set Real ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianTruncatedMomentRealIntegrable
    (b : ℝ) (hb : 0 < b) :
    IntegrableOn
      (fun x : ℝ =>
        (min 1 (x ^ 2)) *
          ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
            Real.exp (-(b ^ 2 * x / 2))))
      (Set.Ioi (0 : ℝ)) volume := by
  sorry
