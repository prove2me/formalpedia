-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_exp_clock_product_sections
-- name    : Kyprianou.Ch08.StageB.p2m88_exp_clock_product_sections
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:02:19.713576+00:00
-- url     : https://prove2.me/theorems/73e9bb9f-5ac5-434b-8870-ce3f53bd54f2
-- title:
--   Measurable product sections at an independent exponential clock
-- statement:
--   For an arbitrary measurable nonnegative-time product event, its time-section probability is measurable and its independent exponential-clock integral equals the product event mass with the clock restricted to nonnegative reals.
-- source:
--   Kyprianou (2006), Theorem 8.7, independent exponential-clock killing.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Probability.Distributions.Exponential
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Measurable product sections at an independent exponential clock -/
theorem p2m88_exp_clock_product_sections :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (q : ℝ), 0 < q → ∀ B : Set (Ω × ℝ≥0), MeasurableSet B →
      let f : ℝ≥0 → ℝ≥0∞ := fun t => P ((fun ω : Ω => (ω, t)) ⁻¹' B)
      Measurable f ∧
        (∫⁻ r : ℝ, f r.toNNReal ∂expMeasure q) =
        (P.prod (expMeasure q)) {z : Ω × ℝ | 0 ≤ z.2 ∧ (z.1, z.2.toNNReal) ∈ B} := by
  sorry

end Kyprianou.Ch08.StageB
