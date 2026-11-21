-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_zscale_convolution_series_entire
-- name    : Kyprianou.Ch08.StageB.source_zscale_convolution_series_entire
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:18:02.969188+00:00
-- url     : https://prove2.me/theorems/2bba2059-65b7-4f16-b20f-6e98045ae27f
-- title:
--   Holomorphic integrated causal scale-convolution series for Z (Corollary 8.5)
-- statement:
--   The explicit complex Z-series 1+z sum_n z^n int_0^x W0^{*(n+1)}(y)dy is entire for every x>0 and source-authenticated scale W. The factorial convolution majorant (8.23) uniformly dominates coefficients after integration on [0,x]; use the Proved factorial-bounded entire power series theorem.
-- source:
--   Kyprianou (2006) Chapter 8 Corollary 8.5 and Lemma 8.3, printed pp. 221-222.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Holomorphicity of the integrated causal-convolution Z-scale series. -/
theorem source_zscale_convolution_series_entire
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (x : ℝ) (hx : 0 < x) :
    Differentiable ℂ (fun z : ℂ => 1 + z * ∑' n : ℕ,
        z ^ n * (((∫ y in (0 : ℝ)..x,
          scaleConvolutionPower (W 0) n y) : ℝ) : ℂ)) := by
  sorry

end Kyprianou.Ch08.StageB
