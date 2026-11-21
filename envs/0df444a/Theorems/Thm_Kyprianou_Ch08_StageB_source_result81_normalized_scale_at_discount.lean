-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_normalized_scale_at_discount
-- name    : Kyprianou.Ch08.StageB.source_result81_normalized_scale_at_discount
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T14:20:22.0076+00:00
-- url     : https://prove2.me/theorems/b5430c32-5738-4ad5-9956-e8891a1d6407
-- title:
--   Construction of the normalized scale at a fixed nonnegative discount
-- statement:
--   Construct the normalized descending potential through the Esscher root and the descending ladder renewal representation. Its cumulative value, exponentially untilted, gives the exact scale transform, half-line continuity and monotonicity.
-- source:
--   Kyprianou (2006), Chapter 8, Laplace normalization (8.5). Decomposition of 4a5bedc9-ffce-4d0e-abf0-74c2a8cddb49.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_normalized_scale_at_discount
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ) (q : ℝ) (hq : 0 ≤ q) :
    ∃ w : ℝ → ℝ, IsQScale ψ q w := by
  sorry
