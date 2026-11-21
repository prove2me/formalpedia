-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_real_scale_series_interval_integral_exchange
-- name    : Kyprianou.Ch08.StageB.source_real_scale_series_interval_integral_exchange
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:20:42.014933+00:00
-- url     : https://prove2.me/theorems/0e226ee1-8540-4a53-8dfe-ee299ec1cf8c
-- title:
--   Exchange source real scale factorial convolution power series and finite interval integral
-- statement:
--   For a source-certified scale W and real q≥0, each causal power is interval integrable and uniformly dominated on [0,x] by the proven factorial coefficient majorant. Hence the sequence of interval integrals is summable, and integrals commute with the real source convolution power tsum on [0,x]. Use Mathlib integral_tsum_of_summable_integral_norm and the Proved source factorial bound. This precisely closes the analytic termwise-integral step in Kyprianou Lemma 8.5.
-- source:
--   Kyprianou (2006) Chapter 8 Lemmas 8.3 and 8.5, p221-222.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB
theorem source_real_scale_series_interval_integral_exchange
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (x q : ℝ) (hx : 0 < x) (hq : 0 ≤ q) :
    Summable (fun n : ℕ => q ^ n *
      (∫ y in (0 : ℝ)..x, scaleConvolutionPower (W 0) n y)) ∧
    (∫ y in (0 : ℝ)..x,
      (∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n y)) =
    ∑' n : ℕ, q ^ n *
      (∫ y in (0 : ℝ)..x, scaleConvolutionPower (W 0) n y) := by
  sorry
end Kyprianou.Ch08.StageB
