-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_no_drawdown_null_measurable_of_effective_event
-- name    : Kyprianou.Ch08.StageB.actual_height_no_drawdown_null_measurable_of_effective_event
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T03:31:39.781525+00:00
-- url     : https://prove2.me/theorems/ebcbaae5-bbe0-42a6-ad5b-765aaa18cf55
-- title:
--   Filtered effective event implies raw null measurability
-- statement:
--   Source-faithful replacement for the failed null-measurability publication. The filtered finite-clock effective event is assumed measurable; the raw all-time no-drawdown event follows from the càdlàg rational-time characterization and a.e. transport along hAX. No Open platform theorem is imported. Parent: 47fdba96-7849-46b6-87b0-6cea26c5eadd.
-- source:
--   Source-faithful replacement for the failed null-measurability publication. The filtered finite-clock effective event is assumed measurable; the raw all-time no-drawdown event follows from the càdlàg rational-time characterization and a.e. transport along hAX. No Open platform theorem is imported. Parent: 47fdba96-7849-46b6-87b0-6cea26c5eadd.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.actual_height_no_drawdown_null_measurable_of_effective_event
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (A : SpectrallyNegativeLevy P 𝓕)
    (D : SpectrallyNegativeModel Ω P)
    (hAX : ∀ᵐ ω ∂P, ∀ t, A.X t ω = D.X t ω)
    (b h : ℝ) (hb : 0 < b) (hh : 0 < h)
    (hE : MeasurableSet {ω : Ω |
      twoSidedExitUpTime A b ω < ⊤ ∧ NoDrawdownBeforeUpcrossing A.X b h ω}) :
    NullMeasurableSet {ω : Ω | NoDrawdownBeforeUpcrossing D.X b h ω} P := by
  sorry
