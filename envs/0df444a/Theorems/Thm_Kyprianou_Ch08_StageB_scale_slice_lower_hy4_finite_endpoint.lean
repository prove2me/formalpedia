-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_scale_slice_lower_hy4_finite_endpoint
-- name    : Kyprianou.Ch08.StageB.scale_slice_lower_hy4_finite_endpoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T21:57:50.834351+00:00
-- url     : https://prove2.me/theorems/8f8e3e69-3bf8-48cb-8675-e04286cdff63
-- title:
--   Finite upcrossing endpoint bound for a cadlag spectrally negative path
-- statement:
--   For a cadlag spectrally negative path, a finite strict upcrossing time of a positive level has path value at least that level at the embedded toNNReal time.
-- source:
--   Source-faithful pathwise child of scale_slice_lower_hy4 (795c944f). Insulates the sInf/right-continuity endpoint estimate from the measure-theoretic part of the lower slice.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.scale_slice_lower_hy4_finite_endpoint
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P)
    {d : ℝ} (hd : 0 < d) {ω : Ω} (hcad : IsCadlag (fun t : ℝ≥0 => D.X t ω)) :
    Kyprianou.Ch08.tauPlus D.X d ω ≠ ⊤ →
      ∃ u : ℝ≥0, (u : ℝ≥0∞) = Kyprianou.Ch08.tauPlus D.X d ω ∧ d ≤ D.X u ω := by
  sorry
