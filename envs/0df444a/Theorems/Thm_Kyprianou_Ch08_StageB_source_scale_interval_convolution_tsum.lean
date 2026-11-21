-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_interval_convolution_tsum
-- name    : Kyprianou.Ch08.StageB.source_scale_interval_convolution_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:23:41.985227+00:00
-- url     : https://prove2.me/theorems/7eec4751-f835-4cb2-a0f5-9be59045fce9
-- title:
--   Locally uniform scale convolution series and termwise interval integration
-- statement:
--   For a genuine source q-scale family and fixed x>0, q≥0, the interval integrals of its zero-discount causal convolution coefficients define a summable real series, and integrating the actual W^(q) over [0,x] equals that series. Establish pointwise source scale expansion (8.24), the uniform-on-[0,x] factorial bound (8.23), and justified interchange of tsum and interval integral. This is the exact nontrivial real-agreement step of Corollary 8.5.
-- source:
--   Kyprianou (2006), Lemma 8.3 (8.23)-(8.24), Corollary 8.5, pp.221-222.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory Set

namespace Kyprianou.Ch08.StageB

/-- Genuine scale-function convolution series commutes with the finite interval integral. -/
theorem source_scale_interval_convolution_tsum
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (x : ℝ) (hx : 0 < x) (q : ℝ) (hq : 0 ≤ q) :
    Summable (fun n : ℕ => q ^ n *
      (∫ y in (0 : ℝ)..x, scaleConvolutionPower (W 0) n y)) ∧
    (∫ y in (0 : ℝ)..x, W q y) =
      ∑' n : ℕ, q ^ n *
        (∫ y in (0 : ℝ)..x, scaleConvolutionPower (W 0) n y) := by
  sorry

end Kyprianou.Ch08.StageB
