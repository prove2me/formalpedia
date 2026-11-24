-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_avram_infimum_probability_support
-- name    : Kyprianou.Ch08.StageB.p2m88_avram_infimum_probability_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:47:58.73005+00:00
-- url     : https://prove2.me/theorems/0ab7bdf8-88fc-43d7-8742-44d47efd592a
-- title:
--   Actual exponential-clock negative infimum is a nonnegative probability law
-- statement:
--   The negative running infimum at the independent positive exponential clock has a probability measure supported on the nonnegative half-line.
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

/-- Actual exponential-clock negative infimum is a nonnegative probability law -/
theorem p2m88_avram_infimum_probability_support :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (F : Filtration ℝ≥0 mΩ)
      (X : AvramDividend.Classical.SpectrallyNegativeLevy P F),
      ∀ q : ℝ, 0 < q →
      let ν := (P.prod (expMeasure q)).map
        (fun z : Ω × ℝ => -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ z.2.toNNReal ∧ y = X.X s z.1})
      IsProbabilityMeasure ν ∧ ν (Iio 0) = 0 := by
  sorry

end Kyprianou.Ch08.StageB
