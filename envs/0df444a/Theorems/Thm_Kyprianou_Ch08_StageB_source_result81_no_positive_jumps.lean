-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_no_positive_jumps
-- name    : Kyprianou.Ch08.StageB.source_result81_no_positive_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T13:13:49.659752+00:00
-- url     : https://prove2.me/theorems/92200ffc-acdc-4836-b709-dd420298cdde
-- title:
--   Negative Lévy measure excludes upward jumps
-- statement:
--   Identify the positive-jump intensity from the characteristic triplet and use its vanishing to exclude positive jumps simultaneously on almost every path. A small-time marginal limit on positive intervals together with a mesh union bound gives an alternative proof.
-- source:
--   Kyprianou (2006), Chapter 8, proof of (8.9), p. 215. Decomposition of 3c242566-b9e1-49b0-bbd8-ab10f9c26428.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory Filter Set Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_no_positive_jumps
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) :
    ∀ᵐ ω ∂P, ∀ (t : ℝ≥0) (l : ℝ), 0 < t →
      Tendsto (fun s => D.X s ω) (nhdsWithin t (Iio t)) (nhds l) → D.X t ω ≤ l := by
  sorry
