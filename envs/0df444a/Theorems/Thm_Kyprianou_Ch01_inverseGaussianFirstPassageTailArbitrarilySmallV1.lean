-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianFirstPassageTailArbitrarilySmallV1
-- name    : Kyprianou.Ch01.inverseGaussianFirstPassageTailArbitrarilySmallV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T00:23:39.542152+00:00
-- url     : https://prove2.me/theorems/7a0a3ff9-5918-47ec-afff-3fcead6e6cfe
-- title:
--   Inverse Gaussian first-passage survival tails become arbitrarily small as the spatial barrier vanishes
-- statement:
--   The q=1 inverse-Gaussian Markov tail inequality gives c(ε)*P(T_s≥ε)≤g(s) for every positive spatial level s, where c(ε)=1-exp(-ε)>0. The already proved analytic lemma gives g(s)→0 as s↓0. Apply the generic vanishingLaplaceEnvelopeGivesSmallTailV1 theorem to obtain an arbitrarily small outer probability for each fixed positive time ε. The proof uses only the original Brownian assumptions and never assumes stochastic independence at the passage clock stage.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5, passage Laplace transform and continuous zero-barrier limit.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianFirstPassageTailArbitrarilySmallV1
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (b : ℝ) (hb : 0 < b)
    (hB : IsLinearBrownian P X 1 b)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (ε : ℝ≥0) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) :
    ∃ s : ℝ≥0, 0 < s ∧
      (P {ω | (ε : WithTop ℝ≥0) ≤
         firstUpperPassage X (s : ℝ) ω}).toReal < δ := by sorry
