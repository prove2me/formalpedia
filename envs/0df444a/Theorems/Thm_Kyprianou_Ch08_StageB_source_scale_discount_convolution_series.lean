-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_discount_convolution_series
-- name    : Kyprianou.Ch08.StageB.source_scale_discount_convolution_series
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T00:07:48.733409+00:00
-- url     : https://prove2.me/theorems/6479a6ef-fd6f-4907-86c8-c42912d5a339
-- title:
--   Identify Chapter 8 q-scale family with causal convolution expansion (8.24)
-- statement:
--   For a genuine q-scale family W defined by the spectrally negative source exponent, the real discounted scale W^(q)(x) for all q,x≥0 is equal to the convergent complex-valued series sum_{n≥0} q^n W^(0)^{*(n+1)}(x). The proof requires the causal convolution Laplace product, weighted Fubini/monotone convergence, Laplace uniqueness and boundary continuity. This is the exact identity (8.24).
-- source:
--   Kyprianou (2006), Chapter 8, Lemma 8.3 equation (8.24), printed p. 221.

import Mathlib.Analysis.Analytic.Basic
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Identification (8.24) of actual q-scale functions with causal convolution series. -/
theorem source_scale_discount_convolution_series :
    ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      HasSourceScaleFamily ψ W →
      ∀ (x q : ℝ), 0 ≤ x → 0 ≤ q →
        ((W q x : ℝ) : ℂ) =
          ∑' n : ℕ, (q : ℂ) ^ n *
            ((scaleConvolutionPower (W 0) n x : ℝ) : ℂ) := by
  sorry

end Kyprianou.Ch08.StageB
