-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_zscale_convolution_series_agrees
-- name    : Kyprianou.Ch08.StageB.source_zscale_convolution_series_agrees
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:18:03.89319+00:00
-- url     : https://prove2.me/theorems/045caeed-7ce9-4bc2-bd12-631334d35b6f
-- title:
--   Source Z-scale equals integrated convolution power series on q≥0
-- statement:
--   For each real q≥0, the explicitly integrated causal convolution series equals Z^(q)(x)=1+q int_0^x W^(q)(y)dy. Use the exact source scale convolution expansion (8.24), locally uniform factorial majorant, interchange of uniformly convergent series with integration, and the original Zscale definition. This is the real-boundary half of Corollary 8.5.
-- source:
--   Kyprianou (2006) Chapter 8 Corollary 8.5 and Lemma 8.3 equation (8.24), pp. 221-222.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Real restriction of the integrated causal-convolution Z-scale series. -/
theorem source_zscale_convolution_series_agrees
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (x : ℝ) (hx : 0 < x)
    (q : ℝ) (hq : 0 ≤ q) :
    (fun z : ℂ => 1 + z * ∑' n : ℕ,
        z ^ n * (((∫ y in (0 : ℝ)..x,
          scaleConvolutionPower (W 0) n y) : ℝ) : ℂ)) (q : ℂ) = (Zscale q (W q) x : ℂ) := by
  sorry

end Kyprianou.Ch08.StageB
