-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaImaginaryDampingEnvelopeIntegrable
-- name    : Kyprianou.Ch01.stableGammaImaginaryDampingEnvelopeIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:04:34.97245+00:00
-- url     : https://prove2.me/theorems/994e6583-5261-4e55-82a7-a50bd948dfad
-- title:
--   Lebesgue-integrable positive-half-line domination envelope for imaginary-axis Gamma Fourier kernel
-- statement:
--   The uniform majorant (‖w‖+2)*(x^(−alpha) for 0<x≤1 and x^(−alpha−1) for x>1) is Lebesgue-integrable on positive reals whenever 0<alpha<1. It follows from the already Proved stableGammaPowerEnvelopeIntegrable theorem with near-zero coefficient one, scaled by the positive constant ‖w‖+2. This supplies integrability for the dominated-convergence passage to imaginary Fourier arguments.
-- source:
--   Kyprianou (2006) Chapter 1 stable index 0<alpha<1; exact Fourier-Gamma dominated-convergence source.

import Mathlib
open MeasureTheory Set Complex Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaImaginaryDampingEnvelopeIntegrable
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1) (w : ℂ) :
    IntegrableOn
      (fun x : ℝ => (‖w‖ + 2) *
        (if x ≤ 1 then x ^ (-alpha) else x ^ (-alpha - 1)))
      (Set.Ioi (0 : ℝ)) volume := by
  sorry
