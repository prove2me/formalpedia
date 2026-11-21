-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_brownian_zero_scale_positive
-- name    : Kyprianou.Ch08.StageB.source_brownian_zero_scale_positive
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T12:46:43.287821+00:00
-- url     : https://prove2.me/theorems/ab2aa7cf-1e53-4b77-976d-f33e2dda0d19
-- title:
--   Source-certified Brownian zero-discount scale is 2x on positive reserves
-- statement:
--   For a genuine source scale family with Brownian Laplace exponent ψ(v)=v²/2, the zero-discount scale function W0 is 2x for every x>0. Both the source scale and the candidate 2x are continuous and nonnegative; the source scale q0 Laplace transform equals 2/θ², and the independently Proved positive_linear_laplace theorem supplies the same transform for 2x. Apply the Proved positive-halfline Laplace uniqueness theorem.
-- source:
--   Kyprianou (2006) Chapter 8 Exercise 8.2(iv).

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB
theorem source_brownian_zero_scale_positive
    (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily (fun v : ℝ => v ^ 2 / 2) W) :
    ∀ x : ℝ, 0 < x → W 0 x = 2 * x := by
  sorry
end Kyprianou.Ch08.StageB
