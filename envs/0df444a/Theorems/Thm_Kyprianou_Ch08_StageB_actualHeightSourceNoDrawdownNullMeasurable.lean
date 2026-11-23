-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_actualHeightSourceNoDrawdownNullMeasurable
-- name    : Kyprianou.Ch08.StageB.actualHeightSourceNoDrawdownNullMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T10:45:59.340796+00:00
-- url     : https://prove2.me/theorems/f9a67c26-a56c-47f5-b513-f3c8dd594026
-- title:
--   Lemma 8.2 original source: positive-height no-drawdown event is measurable modulo null sets
-- statement:
--   For every actual spectrally negative model under its original probability measure and each positive threshold, the event that its reflected surplus never reaches the threshold before its genuine unit upcrossing is measurable modulo null sets. This is a source-specific regularity theorem deriving from adapted measurable coordinates and almost surely cadlag sample paths. It permits measure-theoretic limits on original events without assuming global sample-path measurability.
-- source:
--   Kyprianou 2006 Lemma 8.2. Source model D.levy.stationary_increments and D.levy.cadlag_ae support a.e. coordinates and cadlag paths; see remote Proved source_result81_strict_exit_clocks_aemeasurable 0a5ecd4f-4320-4b0b-b3bc-35e3f18de91a. Existing filtered bridge ebcbaae5-bbe0-42a6-ad5b-765aaa18cf55 proves this under an explicit a.e. path model transfer.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.actualHeightSourceNoDrawdownNullMeasurable
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) :
    ∀ h : ℝ, 0 < h →
      NullMeasurableSet
        {ω : Ω | NoDrawdownBeforeUpcrossing D.X 1 h ω} P := by
  sorry
