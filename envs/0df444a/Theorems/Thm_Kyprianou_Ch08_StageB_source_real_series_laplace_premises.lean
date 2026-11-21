-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_real_series_laplace_premises
-- name    : Kyprianou.Ch08.StageB.source_real_series_laplace_premises
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:18:41.612035+00:00
-- url     : https://prove2.me/theorems/9855a7a6-4b10-4a70-ba1c-12e293393494
-- title:
--   Exact exponentially weighted source series Laplace transform and integrability
-- statement:
--   For every source q≥0 choose a large common root threshold b. Above b the weighted source real series ∑q^n F_n is integrable on (0,∞) and its Laplace transform is exactly 1/(ψθ−q). Use the independently proved scaled geometric source-series Laplace identity and the source weighted convolution-power bounds, including q=0 separately. This supplies the transform and integrability half of the source scale uniqueness theorem.
-- source:
--   Kyprianou (2006) Lemma 8.3 (8.24) p221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB

theorem source_real_series_laplace_premises
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 ≤ q) :
    ∃ b : ℝ, ∀ θ : ℝ, b < θ →
      0 ≤ θ ∧ Phi ψ q < θ ∧
      IntegrableOn
        (fun x : ℝ => Real.exp (-(θ * x)) *
          (∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n x))
        (Set.Ioi (0 : ℝ)) volume ∧
      (∫ x in Set.Ioi (0 : ℝ),
        Real.exp (-(θ * x)) *
          (∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n x) ∂volume) =
        (ψ θ - q)⁻¹ := by
  sorry

end Kyprianou.Ch08.StageB
