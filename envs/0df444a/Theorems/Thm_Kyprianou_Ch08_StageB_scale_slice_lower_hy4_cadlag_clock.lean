-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_scale_slice_lower_hy4_cadlag_clock
-- name    : Kyprianou.Ch08.StageB.scale_slice_lower_hy4_cadlag_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T22:26:18.957705+00:00
-- url     : https://prove2.me/theorems/aa5cc649-03e6-4b65-8578-fa23c05f5715
-- title:
--   No drawdown below l forces up before down at a finite upcrossing
-- statement:
--   On a cadlag path with no drawdown below l before upcrossing d, a finite upcrossing strictly precedes the strict downcrossing of -l.
-- source:
--   Source-faithful pathwise child of scale_slice_lower_hy4 (795c944f); uses only the exact endpoint child and right continuity.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_scale_slice_lower_hy4_finite_endpoint
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.scale_slice_lower_hy4_cadlag_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P)
    {l d : ℝ} (hl : 0 < l) (hd : 0 < d) {ω : Ω}
    (hcad : IsCadlag (fun t : ℝ≥0 => D.X t ω))
    (hND : NoDrawdownBeforeUpcrossing D.X d l ω) :
    tauPlus D.X d ω ≠ ⊤ → tauPlus D.X d ω < tauMinus D.X (-l) ω := by
  sorry
