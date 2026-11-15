-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianFirstPassageLaplace
-- name    : Kyprianou.Ch01.inverseGaussianFirstPassageLaplace
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T08:11:12.646102+00:00
-- url     : https://prove2.me/theorems/238d3988-8d28-4177-b3de-f2f94cfa19a2
-- title:
--   §1.2.5 and Exercise 1.6: inverse Gaussian Brownian first-passage transform
-- statement:
--   For Brownian motion with drift b>0 and upward level s>0, its first-passage time is a natural-filtration stopping time whose Laplace transform is exp(−s(√(b²+2q)−b)). This is the subordinator exponent in (1.4) and the transform underlying the inverse Gaussian density of Exercise 1.6. This remains an uncompiled draft theorem. The stopping-time assertion is formulated for an everywhere-continuous sample-path version of the Brownian process, strengthening the a.s.-continuous baseline to ensure raw natural-filtration measurability.
-- source:
--   Kyprianou (2006), Chapter 1, §1.2.5, pp. 8–9, Exercise 1.6.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianFirstPassageLaplace
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (b s : ℝ)
    (hb : 0 < b) (hs : 0 < s)
    (hB : IsLinearBrownian P X 1 b)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)) :
    IsNaturalStoppingTime X (firstUpperPassage X s) ∧
      ∀ q : ℝ, 0 ≤ q →
        (∫ ω, passageLaplace (firstUpperPassage X s) q ω ∂P) =
          Real.exp (-(s * (Real.sqrt (b ^ 2 + 2 * q) - b))) := by
  sorry
