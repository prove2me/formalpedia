-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_weighted_series_terms_pointwise_summable
-- name    : Kyprianou.Ch08.StageB.source_weighted_series_terms_pointwise_summable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:17:08.88776+00:00
-- url     : https://prove2.me/theorems/9401ff56-6fed-4b4b-aa31-31e356ec5380
-- title:
--   Source weighted convolution-power series pointwise summability
-- statement:
--   Exact source-certified q-scale convolution series analytic sublemma required to prove weighted integrability via the previously Proved nonnegative_integrable_tsum_of_summable_integrals. Preserve all source hypotheses; use the proved source Laplace kernel formula, power integrability and positive scale gap as appropriate.
-- source:
--   Kyprianou (2006) Chapter 8 Lemma 8.3 p221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB
theorem source_weighted_series_terms_pointwise_summable
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q θ : ℝ) (hq : 0 ≤ q) :
    ∀ x : ℝ, Summable (fun n : ℕ =>
      Real.exp (-(θ * x)) *
        (q ^ n * scaleConvolutionPower (W 0) n x)) := by
  sorry
end Kyprianou.Ch08.StageB
