-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianReciprocalGaussianIntegral
-- name    : Kyprianou.Ch01.inverseGaussianReciprocalGaussianIntegral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T19:06:04.435687+00:00
-- url     : https://prove2.me/theorems/689fa3ec-6592-46f4-91eb-f557340bb093
-- title:
--   Reciprocal Gaussian inverse-three-halves Laplace integral
-- statement:
--   For a,c>0, the positive-halfline integral of x^(-3/2)exp(-a/x-cx) is exactly sqrt(pi)/sqrt(a) exp(-2 sqrt(a c)). This general real integral is the analytical core of the inverse Gaussian first-passage density Laplace transform, with positivity ensuring integrability.
-- source:
--   Kyprianou (2006) Exercise 1.6(iii), inverse Gaussian first-passage law, reciprocal Gaussian integral.

import Mathlib
open MeasureTheory Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianReciprocalGaussianIntegral
    (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    (∫ x in Set.Ioi (0 : ℝ),
      (x ^ (-(3 / 2 : ℝ))) *
        Real.exp (-(a / x) - c * x) ∂volume) =
    (Real.sqrt Real.pi / Real.sqrt a) *
      Real.exp (-2 * Real.sqrt (a * c)) := by sorry
