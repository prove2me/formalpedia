-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_discount_series_laplace_zero_q
-- name    : Kyprianou.Ch08.StageB.source_discount_series_laplace_zero_q
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:29:54.84663+00:00
-- url     : https://prove2.me/theorems/7548796d-5b05-43a1-bfea-a49e24c29aee
-- title:
--   Source series Laplace identity at zero discount
-- statement:
--   For q=0 the real source scale series collapses to its n=0 coefficient W0, since 0^0=1 and 0^n=0 for n>0. The source scale certificate gives the weighted Laplace integral as (ψβ)⁻¹. This handles the boundary case excluded from geometric q division.
-- source:
--   Kyprianou (2006) Lemma 8.3 (8.24) p221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB
theorem source_discount_series_laplace_zero_q
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (β : ℝ) (hβ : 0 ≤ β) (hroot0 : Phi ψ 0 < β) :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(β * x)) *
      (∑' n : ℕ, (0 : ℝ) ^ n * scaleConvolutionPower (W 0) n x) ∂volume) =
      (ψ β)⁻¹ := by
  sorry
end Kyprianou.Ch08.StageB
