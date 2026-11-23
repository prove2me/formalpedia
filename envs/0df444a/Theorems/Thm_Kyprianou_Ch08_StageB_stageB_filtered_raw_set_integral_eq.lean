-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_stageB_filtered_raw_set_integral_eq
-- name    : Kyprianou.Ch08.StageB.stageB_filtered_raw_set_integral_eq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T03:31:39.600994+00:00
-- url     : https://prove2.me/theorems/8ef01c4b-7059-4374-9c88-a11ff8966da9
-- title:
--   Filtered to raw discounted integral transport
-- statement:
--   Pure almost-everywhere transport of the discounted no-drawdown set integral from the filtered model path to the original model path. It uses only hAX, tauPlus definition and reflectAtSup/runningSup definitions. Parent: 47fdba96-7849-46b6-87b0-6cea26c5eadd.
-- source:
--   Pure almost-everywhere transport of the discounted no-drawdown set integral from the filtered model path to the original model path. It uses only hAX, tauPlus definition and reflectAtSup/runningSup definitions. Parent: 47fdba96-7849-46b6-87b0-6cea26c5eadd.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.stageB_filtered_raw_set_integral_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (A : SpectrallyNegativeLevy P 𝓕)
    (D : SpectrallyNegativeModel Ω P)
    (hAX : ∀ᵐ ω ∂P, ∀ t, A.X t ω = D.X t ω)
    (b h q c : ℝ) :
    (∫ ω in {ω : Ω | NoDrawdownBeforeUpcrossing A.X b h ω},
      c * discountedAt q (tauPlus A.X b ω) ∂P) =
    (∫ ω in {ω : Ω | NoDrawdownBeforeUpcrossing D.X b h ω},
      c * discountedAt q (tauPlus D.X b ω) ∂P) := by
  sorry
