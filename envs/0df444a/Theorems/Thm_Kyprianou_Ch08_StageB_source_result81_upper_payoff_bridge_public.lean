-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_upper_payoff_bridge_public
-- name    : Kyprianou.Ch08.StageB.source_result81_upper_payoff_bridge_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T19:09:10.040088+00:00
-- url     : https://prove2.me/theorems/9e5fab07-1a09-4da2-9038-63eeb3cf60a2
-- title:
--   Real source upper-first payoff equals the Avram exit expectation
-- statement:
--   Almost-sure path equality and the positive-open-clock theorem identify the strict source passage clocks with the all-time Avram clocks. The measurable ENNReal payoff then converts to the real source integral.
-- source:
--   Kyprianou (2006), Chapter 8, equation (8.8). Isolates the payoff bridge between the original source formula and the Avram exit expectation.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_positive_open_clock_eq_all_times
import Theorems.Thm_AvramDividend_Classical_chat03_exact_upperfirst_discount_integrand_measurable
open MeasureTheory ProbabilityTheory Filter Set Topology
open AvramDividend.Classical Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_upper_payoff_bridge_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (D : Kyprianou.Ch08.SpectrallyNegativeModel Ω P)
    {F : Filtration ℝ≥0 mΩ}
    (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hpaths : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, A.X t ω = D.X t ω)
    (q x a : ℝ) :
    Kyprianou.Ch08.StageB.upBeforeDownExpectation P D.X q x a =
      (AvramDividend.Classical.twoSidedExitExpectation A q a x).toReal := by sorry
