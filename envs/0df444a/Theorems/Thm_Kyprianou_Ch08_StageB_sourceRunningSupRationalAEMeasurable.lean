-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_sourceRunningSupRationalAEMeasurable
-- name    : Kyprianou.Ch08.StageB.sourceRunningSupRationalAEMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T12:27:25.507749+00:00
-- url     : https://prove2.me/theorems/2474ab10-2d7e-443d-8497-d6f7e6455b8c
-- title:
--   Lemma 8.2 source path: running supremum of the genuine spectrally negative Lévy process has measurable rational-time sections
-- statement:
--   For each nonnegative rational time, the genuine source spectrally negative Lévy process has an almost-everywhere measurable running supremum. Prove using the source model's almost-sure cadlag paths and almost-sure measurable time coordinates; express the finite-prefix supremum as a countable supremum over a dense rational schedule plus the endpoint. The AvramDividend.Classical.dense_timeSup_with_endpoint theorem is a Proved general deterministic supporting result. Preserve the original source-model law and probability measure.
-- source:
--   Chapter 8 Lemma 8.2, source no-drawdown event. Needed to close sourceReflectedRationalCoordinatesAEMeasurable bbb3a632-36a6-45e2-8332-7c6135ae05ff, which is an imported Open child of accepted source-specific sketch f9a67c26-a56c-47f5-b513-f3c8dd594026. Reuse general Proved AvramDividend.Classical.dense_timeSup_with_endpoint UUID 4cdf4ed6-71c6-4948-849b-8bfefa587f36.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.sourceRunningSupRationalAEMeasurable
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) :
    ∀ r : ℚ, 0 ≤ r →
      AEMeasurable
        (fun ω => runningSup D.X (r : ℝ).toNNReal ω) P := by
  sorry
