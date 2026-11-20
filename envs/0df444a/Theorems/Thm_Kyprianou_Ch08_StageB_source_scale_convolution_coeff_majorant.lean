-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_convolution_coeff_majorant
-- name    : Kyprianou.Ch08.StageB.source_scale_convolution_coeff_majorant
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T00:15:45.239749+00:00
-- url     : https://prove2.me/theorems/8a92fb29-cac7-4768-93e9-84f9bf559b33
-- title:
--   Factorial bound on complex coefficients of source scale powers
-- statement:
--   The factorial majorant for convolution powers implies a bound on the complex coefficient norms by W(0,x)(x W(0,x))^n/n!, once local integrability is available. Combine the Proved positivity lemma and the general factorial majorant. Directly enables entire extension in Lemma 8.3.
-- source:
--   Kyprianou (2006), Chapter 8 Lemma 8.3, (8.23), printed p. 221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Kyprianou.Ch08.StageB

/-- Quantitative factorial bound on complexified scale coefficients. -/
theorem source_scale_convolution_coeff_majorant
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (hint : ∀ (n : ℕ) (x : ℝ), 0 ≤ x →
      IntegrableOn (fun s : ℝ => W 0 s * scaleConvolutionPower (W 0) n (x - s))
        (Set.Ioc (0 : ℝ) x) volume)
    (x : ℝ) (hx : 0 ≤ x) :
    ∀ n : ℕ,
      ‖((scaleConvolutionPower (W 0) n x : ℝ) : ℂ)‖ ≤
        W 0 x * (x * W 0 x) ^ n / (Nat.factorial n : ℝ) := by
  sorry

end Kyprianou.Ch08.StageB
