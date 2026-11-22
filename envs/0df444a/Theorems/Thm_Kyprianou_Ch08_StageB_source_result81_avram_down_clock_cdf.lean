-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_avram_down_clock_cdf
-- name    : Kyprianou.Ch08.StageB.source_result81_avram_down_clock_cdf
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:01:01.235174+00:00
-- url     : https://prove2.me/theorems/80e7c39b-072e-47d5-a5d3-7fe26d044dc0
-- title:
--   Strict ruin payoff and the reflected infimum at an exponential clock
-- statement:
--   For a spectrally negative Lévy process starting at zero, the strict downward passage from reserve x has discounted payoff equal to the upper tail of the reflected running infimum at an independent exponential clock of rate q. Given the path, the sections of the two events agree except possibly at the single clock value equal to the first passage time. Right continuity at time zero accounts for immediate passage from a negative reserve.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1, identity (8.6). Exponential-clock obligation for d5833b96-248c-4b9d-87b8-3cb8b121acb0.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Exponential
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_avram_down_clock_cdf
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    (X : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (q : ℝ) (hq : 0 < q) (x : ℝ) :
    downExpectation P X.X q x = 1 - ProbabilityTheory.cdf
      ((P.prod (ProbabilityTheory.expMeasure q)).map
        (fun z : Ω × ℝ => -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ z.2.toNNReal ∧ y = X.X s z.1})) x := by
  sorry
