-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_weighted_series_integral_masses_summable
-- name    : Kyprianou.Ch08.StageB.source_weighted_series_integral_masses_summable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:17:07.829212+00:00
-- url     : https://prove2.me/theorems/c7e1d655-5191-4d4a-a5ad-6b69ef9df36f
-- title:
--   Source weighted convolution-power integral masses sum geometrically
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
theorem source_weighted_series_integral_masses_summable
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q θ : ℝ) (hq : 0 ≤ q) (hθ : 0 ≤ θ)
    (hroot0 : Phi ψ 0 < θ) (hrootq : Phi ψ q < θ) :
    Summable (fun n : ℕ =>
      ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (q ^ n * scaleConvolutionPower (W 0) n x) ∂volume) := by
  sorry
end Kyprianou.Ch08.StageB
