-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_avram_clock_pair_product
-- name    : Kyprianou.Ch08.StageB.p2m88_avram_clock_pair_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:48:19.427621+00:00
-- url     : https://prove2.me/theorems/83e15286-a6a1-46b1-9684-da30a660b86a
-- title:
--   Actual exponential-clock overshoot and negative-infimum product law
-- statement:
--   On the existing Avram spectrally negative path model, with q positive and positive root phi, the actual pair consisting of terminal process minus running infimum and negative running infimum is measurable and its joint clock law is the product of the rate-phi exponential measure and the negative-infimum marginal.
-- source:
--   Kyprianou (2006), proof of Theorem 8.7, Wiener–Hopf decomposition at the exponential time.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Exponential
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Actual exponential-clock overshoot and negative-infimum product law -/
theorem p2m88_avram_clock_pair_product :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (F : Filtration ℝ≥0 mΩ)
      (X : AvramDividend.Classical.SpectrallyNegativeLevy P F),
      ∀ q φ : ℝ, 0 < q → 0 < φ → X.ψ φ = q →
      let M := P.prod (expMeasure q)
      let I : Ω × ℝ → ℝ := fun z : Ω × ℝ => -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ z.2.toNNReal ∧ y = X.X s z.1}
      let J : Ω × ℝ → ℝ × ℝ :=
        fun z => (X.X z.2.toNNReal z.1 + I z, I z)
      Measurable J ∧ M.map J = (expMeasure φ).prod (M.map I) := by
  sorry

end Kyprianou.Ch08.StageB
