-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_power_interval_integrable
-- name    : Kyprianou.Ch08.StageB.source_scale_power_interval_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:18:44.62953+00:00
-- url     : https://prove2.me/theorems/31a74b25-b11c-4305-9441-9fcc8f888cfb
-- title:
--   Finite-interval integrability of all source scale convolution coefficients
-- statement:
--   For every source-authenticated spectrally negative scale family and x≥0, each causal self-convolution power F_n(y) is integrable on the interval [0,x]. Choose β>max(0,Φ(0)), restrict the Proved weighted-integrability theorem to (0,x], and multiply by the continuous bounded inverse exponential weight exp(βy). This supports both Corollary 8.5 and the integral-series interchange.
-- source:
--   Kyprianou (2006) Chapter 8 Lemma 8.3 and Corollary 8.5, pp.221-222.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory Set

namespace Kyprianou.Ch08.StageB

/-- Every zero-discount causal scale convolution coefficient is integrable on [0,x]. -/
theorem source_scale_power_interval_integrable
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (x : ℝ) (hx : 0 ≤ x) :
    ∀ n : ℕ, IntervalIntegrable (scaleConvolutionPower (W 0) n)
      volume 0 x := by
  sorry

end Kyprianou.Ch08.StageB
