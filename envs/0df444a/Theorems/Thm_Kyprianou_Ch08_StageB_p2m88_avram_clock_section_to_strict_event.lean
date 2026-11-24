-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_avram_clock_section_to_strict_event
-- name    : Kyprianou.Ch08.StageB.p2m88_avram_clock_section_to_strict_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:58:22.301868+00:00
-- url     : https://prove2.me/theorems/e2ff40d5-6d56-4142-8b7c-d5bf65c9a757
-- title:
--   Strict lower-killed time sections and their exponential product-clock mass
-- statement:
--   The probabilities of strict lower survival and terminal membership are measurable functions of nonnegative time. Their exponential-clock integral is the actual strict lower-killed product-clock event mass.
-- source:
--   Kyprianou (2006), proof of Theorem 8.7, independent exponential killing.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Probability.Distributions.Exponential
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Strict lower-killed time sections and their exponential product-clock mass -/
theorem p2m88_avram_clock_section_to_strict_event :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (F : Filtration ℝ≥0 mΩ)
      (X : AvramDividend.Classical.SpectrallyNegativeLevy P F),
      ∀ q x : ℝ, 0 < q → 0 ≤ x → ∀ A : Set ℝ, MeasurableSet A →
      let f : ℝ≥0 → ℝ≥0∞ := fun t =>
        P {ω | (t : WithTop ℝ≥0) <
          tauMinus (shifted X.X x) 0 ω ∧ shifted X.X x t ω ∈ A}
      Measurable f ∧
        (∫⁻ r : ℝ, f r.toNNReal ∂expMeasure q) =
        (P.prod (expMeasure q)) {z : Ω × ℝ | 0 ≤ z.2 ∧
          ENNReal.ofReal z.2 < AvramDividend.Classical.twoSidedExitDownTime X (-x) z.1 ∧
          x + X.X z.2.toNNReal z.1 ∈ A} := by
  sorry

end Kyprianou.Ch08.StageB
