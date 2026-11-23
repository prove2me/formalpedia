-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_stageB_filtered_effective_integral_of_nullmeas
-- name    : Kyprianou.Ch08.StageB.stageB_filtered_effective_integral_of_nullmeas
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T03:31:26.709495+00:00
-- url     : https://prove2.me/theorems/4f352914-2150-4111-9215-ecbef4323d49
-- title:
--   Filtered effective-domain integral reduction
-- statement:
--   Effective-domain reduction for a filtered spectrally negative Levy path. The difference between the no-drawdown event and its finite-clock part lies where tauPlus is top, and discountedAt q top = 0. The exact premise is NullMeasurableSet, matching MeasureTheory.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero. Parent: 47fdba96-7849-46b6-87b0-6cea26c5eadd.
-- source:
--   Effective-domain reduction for a filtered spectrally negative Levy path. The difference between the no-drawdown event and its finite-clock part lies where tauPlus is top, and discountedAt q top = 0. The exact premise is NullMeasurableSet, matching MeasureTheory.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero. Parent: 47fdba96-7849-46b6-87b0-6cea26c5eadd.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.stageB_filtered_effective_integral_of_nullmeas
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (b h c q : ℝ)
    (hN : NullMeasurableSet {ω : Ω | NoDrawdownBeforeUpcrossing X.X b h ω} P) :
    (∫ ω in {ω : Ω | NoDrawdownBeforeUpcrossing X.X b h ω},
      c * discountedAt q (tauPlus X.X b ω) ∂P) =
    (∫ ω in {ω : Ω | tauPlus X.X b ω < ⊤ ∧ NoDrawdownBeforeUpcrossing X.X b h ω},
      c * discountedAt q (tauPlus X.X b ω) ∂P) := by
  sorry
