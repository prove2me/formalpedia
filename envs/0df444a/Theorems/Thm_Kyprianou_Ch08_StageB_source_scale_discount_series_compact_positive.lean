-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_discount_series_compact_positive
-- name    : Kyprianou.Ch08.StageB.source_scale_discount_series_compact_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:24:24.124713+00:00
-- url     : https://prove2.me/theorems/38fb130d-bd73-4f88-9dbb-53f8e9e3491d
-- title:
--   Uniformly convergent source real scale convolution series on a compact positive-reserve interval
-- statement:
--   For every q≥0 and compact interval [a,R] inside the positive reserve halfline, each source causal convolution power is continuous and its factorial majorant is uniformly summable, so the infinite real discount scale series is continuous on [a,R] by Mathlib continuousOn_tsum. The a>0 restriction avoids needing boundary regularity at zero.
-- source:
--   Kyprianou (2006) Chapter 8 Lemma 8.3 bound (8.23), p221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB
theorem source_scale_discount_series_compact_positive
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q a R : ℝ) (hq : 0 ≤ q) (ha : 0 < a) (hR : a ≤ R) :
    ContinuousOn (fun x : ℝ => ∑' n : ℕ,
      q ^ n * scaleConvolutionPower (W 0) n x)
      (Set.Icc a R) := by
  sorry
end Kyprianou.Ch08.StageB
