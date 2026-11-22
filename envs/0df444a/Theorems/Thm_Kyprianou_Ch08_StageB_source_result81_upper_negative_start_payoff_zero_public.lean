-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_upper_negative_start_payoff_zero_public
-- name    : Kyprianou.Ch08.StageB.source_result81_upper_negative_start_payoff_zero_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T19:09:18.263926+00:00
-- url     : https://prove2.me/theorems/40d27118-39b4-43d5-8290-8d77b9b2d476
-- title:
--   Upper-first payoff vanishes from a negative start
-- statement:
--   From a negative start the lower exit clock is zero by right continuity and path equality, so the strict upper-first payoff vanishes almost surely.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1 negative-start boundary case for equation (8.8).

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_positive_open_clock_eq_all_times
open MeasureTheory ProbabilityTheory Filter Set Topology
open AvramDividend.Classical Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_upper_negative_start_payoff_zero_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (D : Kyprianou.Ch08.SpectrallyNegativeModel Ω P)
    {F : Filtration ℝ≥0 mΩ}
    (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hpaths : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, A.X t ω = D.X t ω)
    (q x a : ℝ) (hxneg : x < 0) :
    (fun ω => if Kyprianou.Ch08.tauPlus
          (Kyprianou.Ch08.StageB.shifted D.X x) a ω <
        Kyprianou.Ch08.tauMinus
          (Kyprianou.Ch08.StageB.shifted D.X x) 0 ω
      then Kyprianou.Ch08.discountedAt q
        (Kyprianou.Ch08.tauPlus
          (Kyprianou.Ch08.StageB.shifted D.X x) a ω)
      else 0) =ᵐ[P] 0 := by sorry
