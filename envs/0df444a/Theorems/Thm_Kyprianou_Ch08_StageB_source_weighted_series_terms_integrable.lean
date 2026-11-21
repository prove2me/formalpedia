-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_weighted_series_terms_integrable
-- name    : Kyprianou.Ch08.StageB.source_weighted_series_terms_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:17:08.515564+00:00
-- url     : https://prove2.me/theorems/35fa0fee-7154-48ce-a593-d63c9c46fb3c
-- title:
--   Each discounted source convolution-power coefficient is weighted integrable
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
theorem source_weighted_series_terms_integrable
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q θ : ℝ) (hq : 0 ≤ q) (hθ : 0 ≤ θ)
    (hroot0 : Phi ψ 0 < θ) :
    ∀ n : ℕ, IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) *
        (q ^ n * scaleConvolutionPower (W 0) n x))
      (Set.Ioi (0 : ℝ)) volume := by
  sorry
end Kyprianou.Ch08.StageB
