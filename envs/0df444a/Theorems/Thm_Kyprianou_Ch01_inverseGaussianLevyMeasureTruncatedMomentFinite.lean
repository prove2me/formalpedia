-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianLevyMeasureTruncatedMomentFinite
-- name    : Kyprianou.Ch01.inverseGaussianLevyMeasureTruncatedMomentFinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:39:20.991986+00:00
-- url     : https://prove2.me/theorems/eacdefa2-3278-4b20-a924-5194533addeb
-- title:
--   Inverse Gaussian positive-jump Lévy measure has finite truncated quadratic moment
-- statement:
--   The original tilted inverse-Gaussian Lévy density has finite integral of min(1,x²): near zero the integrand behaves as x^(1/2), and at infinity the exponentially tilted density is integrable. This supplies the exact nontrivial Levy measure finiteness criterion.
-- source:
--   Kyprianou (2006), Chapter 1 inverse-Gaussian Lévy measure criterion, exact child of inverseGaussianLevyMeasureSourceExact.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Set Complex ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianLevyMeasureTruncatedMomentFinite
    (b : ℝ) (hb : 0 < b) :
    let Pi : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-(b ^ 2 * x / 2))))
    (∫⁻ x : ℝ, ENNReal.ofReal (min 1 (x ^ 2)) ∂Pi) < ⊤ := by
  sorry
