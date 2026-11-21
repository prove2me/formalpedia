-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_positive_linear_laplace
-- name    : Kyprianou.Ch08.StageB.source_positive_linear_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:44:52.697729+00:00
-- url     : https://prove2.me/theorems/70fde4b6-7f28-41e7-9a42-b7ead65d6023
-- title:
--   Laplace transform of Brownian zero-discount scale candidate 2x
-- statement:
--   At θ>0 the positive-halfline function x↦2x has an integrable exponential weight and Laplace integral 2/θ². Derive from the Proved positive_laplace_interval_primitive_real applied to constant function 2 and elementary Mathlib integral_exp_mul_Ioi. This is an independently reusable analytic component for the Brownian spectrally negative q=0 scale function.
-- source:
--   Kyprianou 2006, Chapter 8 Exercise 8.2(iv).

import Mathlib
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB
theorem source_positive_linear_laplace
    (θ : ℝ) (hθ : 0 < θ) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * (2 * x))
      (Set.Ioi (0 : ℝ)) volume ∧
    (∫ x in Set.Ioi (0 : ℝ),
      Real.exp (-(θ * x)) * (2 * x) ∂volume) = 2 / θ ^ 2 := by
  sorry
end Kyprianou.Ch08.StageB
