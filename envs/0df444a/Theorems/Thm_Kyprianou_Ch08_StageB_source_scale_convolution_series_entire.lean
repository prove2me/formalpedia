-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_convolution_series_entire
-- name    : Kyprianou.Ch08.StageB.source_scale_convolution_series_entire
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T00:07:46.002195+00:00
-- url     : https://prove2.me/theorems/d2678bca-8f68-49a9-bb2a-a172156e7219
-- title:
--   Convolution scale power series is complex entire (Lemma 8.3)
-- statement:
--   Under the actual Chapter 8 source scale-family hypotheses, the function z↦∑_{n≥0} z^n W_0^{*(n+1)}(x), for every fixed x≥0, is complex differentiable everywhere. This follows from the factorial majorant (8.23) and uniform convergence of the power series and derivatives on compact discs. It is the analytic half of Lemma 8.3.
-- source:
--   Kyprianou (2006), Chapter 8, Lemma 8.3 equations (8.23) and (8.24), printed p. 221.

import Mathlib.Analysis.Analytic.Basic
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Entire complex dependence of the scale-function causal convolution series. -/
theorem source_scale_convolution_series_entire :
    ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      HasSourceScaleFamily ψ W →
      ∀ (x : ℝ), 0 ≤ x →
        Differentiable ℂ (fun z : ℂ =>
          ∑' n : ℕ, z ^ n *
            ((scaleConvolutionPower (W 0) n x : ℝ) : ℂ)) := by
  sorry

end Kyprianou.Ch08.StageB
