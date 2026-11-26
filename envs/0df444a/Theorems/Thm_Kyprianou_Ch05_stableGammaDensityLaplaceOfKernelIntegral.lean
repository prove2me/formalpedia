-- Prove2me | Theorems.Thm_Kyprianou_Ch05_stableGammaDensityLaplaceOfKernelIntegral
-- name    : Kyprianou.Ch05.stableGammaDensityLaplaceOfKernelIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:44:37.42067+00:00
-- url     : https://prove2.me/theorems/7513a5ca-1d54-4f75-9278-a1f97be5c142
-- title:
--   Stable Gamma density Laplace lintegral from real kernel identity
-- statement:
--   Convert the real Gamma kernel identity into the nonnegative Laplace transform of the candidate stable potential density. Nonnegativity and the positive real kernel integral justify integrability; use withDensity, Gamma positivity and power algebra.
-- source:
--   Kyprianou (2006), Exercise 5.6(ii), solution p. 325; Chapter 1 stableGammaKernelIntegral.

import Mathlib
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch05.stableGammaDensityLaplaceOfKernelIntegral
    (alpha theta : Real) (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (ht : 0 < theta)
    (hKernel : (∫ x in Set.Ioi (0 : Real),
      Real.exp (-(theta * x)) * x ^ (alpha - 1) ∂volume) =
      (1 / theta) ^ alpha * Real.Gamma alpha) :
    (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂
      ((volume.restrict (Set.Ioi (0 : Real))).withDensity
        (fun z : Real => ENNReal.ofReal (z ^ (alpha - 1) / Real.Gamma alpha)))) =
        (ENNReal.ofReal (theta ^ alpha))⁻¹ := by
  sorry
