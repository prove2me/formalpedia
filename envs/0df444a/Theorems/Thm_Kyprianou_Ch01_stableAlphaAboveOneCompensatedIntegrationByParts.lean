-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneCompensatedIntegrationByParts
-- name    : Kyprianou.Ch01.stableAlphaAboveOneCompensatedIntegrationByParts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:24:17.708719+00:00
-- url     : https://prove2.me/theorems/cee92e5c-c2e8-4b7a-9032-94aee4c3ac33
-- title:
--   Stable alpha above one compensated Fourier integral integration by parts to alpha minus one deficit
-- statement:
--   For 1<alpha<2 the exact original compensated complex stable Fourier kernel integrates by parts to i/alpha times the alpha−1 uncompensated complex deficit integral. The two integration-by-parts boundary contributions vanish: exp(ir)−1−ir is O(r²) at zero and O(r) at infinity. This reduces the analytic α>1 case to the 0<alpha−1<1 integral already represented by stableGammaComplexDeficitValueImaginary.
-- source:
--   Kyprianou (2006) Chapter 1 stable characteristic exponents, exact compensated integration by parts.

import Mathlib
open MeasureTheory Set Complex Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaAboveOneCompensatedIntegrationByParts
    (alpha : ℝ) (h1 : 1 < alpha) (h2 : alpha < 2) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) /
          ((((r : ℝ) ^ (alpha + 1)) : ℝ) : ℂ)
      ∂volume) =
      (Complex.I / (alpha : ℂ)) *
        (∫ r in Set.Ioi (0 : ℝ),
          (Complex.exp (Complex.I * (r : ℂ)) - 1) *
            (((r ^ (- (alpha - 1) - 1) : ℝ)) : ℂ)
          ∂volume) := by
  sorry
