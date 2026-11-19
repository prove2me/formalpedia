-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianLevyMeasureSourceExact
-- name    : Kyprianou.Ch01.inverseGaussianLevyMeasureSourceExact
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T00:37:45.357342+00:00
-- url     : https://prove2.me/theorems/8ff88bce-69c2-4c1b-9406-a9b89c89563a
-- title:
--   Inverse-Gaussian tilted three-half-density is a Lévy measure
-- statement:
--   The original positive inverse-Gaussian tilted x^(-3/2) density, with exp(-b²x/2), defines a Lévy measure on ℝ for all b>0, with zero atom and finite truncated second moment.
-- source:
--   Kyprianou (2006), Chapter 1 inverse-Gaussian Lévy exponent and Lévy measure, source-exact child.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Set Complex ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianLevyMeasureSourceExact
    (b : ℝ) (hb : 0 < b) :
    let Pi : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-(b ^ 2 * x / 2))))
    IsLevyMeasure Pi := by
  sorry
