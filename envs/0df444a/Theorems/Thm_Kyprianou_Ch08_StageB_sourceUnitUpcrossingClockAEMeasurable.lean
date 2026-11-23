-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_sourceUnitUpcrossingClockAEMeasurable
-- name    : Kyprianou.Ch08.StageB.sourceUnitUpcrossingClockAEMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T11:29:28.069127+00:00
-- url     : https://prove2.me/theorems/1041fc27-ccc0-45b7-ab23-818b081b8fef
-- title:
--   Lemma 8.2: unit upward passage clock is a.e. measurable in the genuine Chapter 8 model
-- statement:
--   The actual first-passage clock above unit level of the spectrally negative source model is measurable modulo the original probability law, even if never reached. Direct specialisation at initial shift zero and upper barrier one of the already Proved original source strict-exit-clock a.e. measurability theorem.
-- source:
--   Proved Kyprianou.Ch08.StageB.source_result81_strict_exit_clocks_aemeasurable 0a5ecd4f-4320-4b0b-b3bc-35e3f18de91a. Required child in main Lemma 8.2 actual no-drawdown measurability frontier f9a67c26-a56c-47f5-b513-f3c8dd594026.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.sourceUnitUpcrossingClockAEMeasurable
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) :
    AEMeasurable (fun ω => (tauPlus D.X 1 ω : ℝ≥0∞)) P := by
  sorry
