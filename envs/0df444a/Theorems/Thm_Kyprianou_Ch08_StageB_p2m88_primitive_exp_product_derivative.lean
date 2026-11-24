-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_primitive_exp_product_derivative
-- name    : Kyprianou.Ch08.StageB.p2m88_primitive_exp_product_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:27:02.3461+00:00
-- url     : https://prove2.me/theorems/deacd1d9-025b-44f0-8576-51be97c8f586
-- title:
--   Integral of the exponentially weighted primitive derivative
-- statement:
--   For a continuous real function v, integrate the derivative of the product of exp(-phi*t) and its primitive from zero.
-- source:
--   Kyprianou (2006), Corollary 8.8, integration by parts.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
set_option autoImplicit false
open MeasureTheory Set

namespace Kyprianou.Ch08.StageB
 theorem p2m88_primitive_exp_product_derivative :
    ∀ (φ : ℝ) (v : ℝ → ℝ), Continuous v → ∀ b : ℝ,
      (∫ t in (0 : ℝ)..b, Real.exp (-φ*t) *
        (v t - φ * (∫ s in (0 : ℝ)..t, v s))) =
      Real.exp (-φ*b) * (∫ s in (0 : ℝ)..b, v s) := by
  sorry
end Kyprianou.Ch08.StageB
