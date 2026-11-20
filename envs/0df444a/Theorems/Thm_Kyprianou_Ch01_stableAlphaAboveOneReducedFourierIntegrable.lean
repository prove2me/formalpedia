-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneReducedFourierIntegrable
-- name    : Kyprianou.Ch01.stableAlphaAboveOneReducedFourierIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:12:55.032947+00:00
-- url     : https://prove2.me/theorems/2756d00f-89b7-4abf-8fe9-0a9b5c6faf32
-- title:
--   Absolute integrability of the reduced α>1 Fourier kernel by the proved α<1 Gamma integrability
-- statement:
--   For 1<alpha<2, the source-exact reduced Fourier integrand (exp(ir)−1)r^(−alpha) is Lebesgue integrable on positive real r. Its exponent is exactly −(alpha−1)−1, where beta=alpha−1 lies in (0,1); instantiate the already Proved stableGammaComplexDeficitIntegrable with beta and w=i. This is the missing genuine second integrability condition for the α>1 infinite-interval integration-by-parts identity.
-- source:
--   Kyprianou (2006), Chapter 1 stable α∈(1,2) Fourier exponent, integration by parts.

import Mathlib
open MeasureTheory Complex Real Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaAboveOneReducedFourierIntegrable
    (alpha : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    IntegrableOn (fun r : ℝ =>
      (Complex.exp (Complex.I * (r : ℂ)) - 1) *
        (((r ^ (-alpha) : ℝ)) : ℂ))
      (Set.Ioi (0 : ℝ)) := by sorry
