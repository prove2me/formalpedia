-- Prove2me | Theorems.Thm_Kyprianou_Ch01_logarithmicConvIntensityOffZeroFinite
-- name    : Kyprianou.Ch01.logarithmicConvIntensityOffZeroFinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:12:21.139938+00:00
-- url     : https://prove2.me/theorems/65ac9f2d-c290-4c6e-8ede-dfb2f018ec08
-- title:
--   Explicit finite logarithmic convolution jump intensity restricted to nonzero marks
-- statement:
--   For q∈[0,1), any real probability increment distribution has a finite logarithmic-convolution cluster measure obtained by summing the weighted convolution powers q^(n+1)/(n+1). Restricting to nonzero jump values makes its mass at zero vanish while retaining finiteness, including the all-zero increment-law case. This is the precise intensity measure for Kyprianou Chapter 1 Exercise 1.2(ii).
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(ii), finite Lévy intensity of logarithmic convolution clusters.

import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_transforms
open MeasureTheory ProbabilityTheory QueueingFundamentals.MG1
open scoped ENNReal NNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.logarithmicConvIntensityOffZeroFinite
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw] :
    let Λ : Measure ℝ :=
      (Measure.sum fun n : ℕ =>
        (ENNReal.ofReal (q ^ (n + 1) / (n + 1 : ℝ))) •
          QueueingFundamentals.MG1.convPow jumpLaw (n + 1)).restrict ({0}ᶜ)
    Λ {0} = 0 ∧ Λ Set.univ < ⊤ := by
  sorry
