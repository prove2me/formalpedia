-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianFirstPassageLaplaceRightContinuous
-- name    : Kyprianou.Ch01.inverseGaussianFirstPassageLaplaceRightContinuous
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T10:01:20.094086+00:00
-- url     : https://prove2.me/theorems/5109b042-f54f-4840-8300-3b46f5ada4c6
-- title:
--   §1.2.5 and Exercise 1.6: inverse Gaussian first-passage transform in right-continuous natural filtration
-- statement:
--   Corrected source theorem: for a pointwise-continuous drifted Brownian process, the strict first entrance above a positive level is a stopping time for the right-continuous natural filtration; its inverse Gaussian Laplace transform is unchanged. The continuity condition explicitly restricts to canonical continuous-path Brownian representatives.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5, Exercise 1.6; Perla Sousi, Advanced Probability (2011), Proposition 3.5.

import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianFirstPassageLaplaceRightContinuous
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (b s : ℝ)
    (hb : 0 < b) (hs : 0 < s)
    (hB : IsLinearBrownian P X 1 b)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)) :
    IsNaturalRightStoppingTime X (firstUpperPassage X s) ∧
      ∀ q : ℝ, 0 ≤ q →
        (∫ ω, passageLaplace (firstUpperPassage X s) q ω ∂P) =
          Real.exp (-(s * (Real.sqrt (b ^ 2 + 2 * q) - b))) := by
  sorry
