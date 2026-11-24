-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_avram_clock_strict_event_to_infimum
-- name    : Kyprianou.Ch08.StageB.p2m88_avram_clock_strict_event_to_infimum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:58:17.814142+00:00
-- url     : https://prove2.me/theorems/905575f3-9311-48bd-80a6-0e0ae48f2d6b
-- title:
--   Actual strict lower survival and running-infimum event have equal clock mass
-- statement:
--   For every Borel terminal set, the strict lower-killed product-clock event and the running-infimum survival event have equal measure at a positive independent exponential clock.
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

/-- Actual strict lower survival and running-infimum event have equal clock mass -/
theorem p2m88_avram_clock_strict_event_to_infimum :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (F : Filtration ℝ≥0 mΩ)
      (X : AvramDividend.Classical.SpectrallyNegativeLevy P F),
      ∀ q x : ℝ, 0 < q → 0 ≤ x → ∀ A : Set ℝ, MeasurableSet A →
      (P.prod (expMeasure q)) {z : Ω × ℝ | 0 ≤ z.2 ∧
          ENNReal.ofReal z.2 < AvramDividend.Classical.twoSidedExitDownTime X (-x) z.1 ∧
          x + X.X z.2.toNNReal z.1 ∈ A} =
      (P.prod (expMeasure q)) {z : Ω × ℝ | (-sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ z.2.toNNReal ∧ y = X.X s z.1}) ≤ x ∧
          x + X.X z.2.toNNReal z.1 ∈ A} := by
  sorry

end Kyprianou.Ch08.StageB
