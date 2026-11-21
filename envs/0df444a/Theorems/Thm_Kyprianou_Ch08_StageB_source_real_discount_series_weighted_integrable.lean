-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_real_discount_series_weighted_integrable
-- name    : Kyprianou.Ch08.StageB.source_real_discount_series_weighted_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:28:59.186582+00:00
-- url     : https://prove2.me/theorems/de51bbc2-1a61-4a7f-a67e-4c75a7458d18
-- title:
--   Absolute weighted integrability of source real scale convolution series
-- statement:
--   For genuine source Wq and q≥0, at any weight θ above both source roots, the exponentially weighted series Σq^nFn is integrable on x>0. Its nonnegative termwise mass is bounded by a geometric series with ratio q/ψθ<1, and Tonelli identifies the sum as integrable. This is the exact weighted-integrability hypothesis for source scale Laplace uniqueness.
-- source:
--   Kyprianou (2006) Lemma 8.3 (8.23)-(8.24), p221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB
theorem source_real_discount_series_weighted_integrable
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q θ : ℝ) (hq : 0 ≤ q) (hθ : 0 ≤ θ)
    (hroot0 : Phi ψ 0 < θ) (hrootq : Phi ψ q < θ) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) *
        (∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n x))
      (Set.Ioi (0 : ℝ)) volume := by
  sorry
end Kyprianou.Ch08.StageB
