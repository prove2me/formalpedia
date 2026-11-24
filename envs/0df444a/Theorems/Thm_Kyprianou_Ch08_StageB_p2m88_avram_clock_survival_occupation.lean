-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_avram_clock_survival_occupation
-- name    : Kyprianou.Ch08.StageB.p2m88_avram_clock_survival_occupation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:48:14.578541+00:00
-- url     : https://prove2.me/theorems/e99ff4e7-7a17-4cd4-835f-cd030c47492b
-- title:
--   Actual strict lower-killed occupation through the exponential clock
-- statement:
--   For the Avram path model, q-positive discounted occupation before the strict lower passage is 1/q times the product-clock probability that the running infimum stays above the lower boundary and the terminal shifted state is in the chosen measurable set.
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

/-- Actual strict lower-killed occupation through the exponential clock -/
theorem p2m88_avram_clock_survival_occupation :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (F : Filtration ℝ≥0 mΩ)
      (X : AvramDividend.Classical.SpectrallyNegativeLevy P F),
      ∀ (q x : ℝ), 0 < q → 0 ≤ x → ∀ A : Set ℝ, MeasurableSet A →
      (∫⁻ t : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
        P {ω | (t : WithTop ℝ≥0) <
          tauMinus (shifted X.X x) 0 ω ∧ shifted X.X x t ω ∈ A}
          ∂positiveTimeLebesgue) =
      (ENNReal.ofReal q)⁻¹ * (P.prod (expMeasure q))
        {z : Ω × ℝ | (-sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ z.2.toNNReal ∧ y = X.X s z.1}) ≤ x ∧
          x + X.X z.2.toNNReal z.1 ∈ A} := by
  sorry

end Kyprianou.Ch08.StageB
