-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianFourierScalarAssoc
-- name    : Kyprianou.Ch01.inverseGaussianFourierScalarAssoc
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T18:48:25.622186+00:00
-- url     : https://prove2.me/theorems/981d07bb-5af3-4dce-b4c7-c776c9f1d2b0
-- title:
--   Real density Fourier scalar rearrangement in complex integral
-- statement:
--   For all real weights a,d,p and complex f, ((a*d)*p) • f = a*(f*p*d) after real-to-complex coercions. This exact nonprobabilistic scalar association is used for the original inverse Gaussian Fourier density.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.6(ii) exponential Lévy density algebra.

import Mathlib
open Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianFourierScalarAssoc
    (a d p : ℝ) (f : ℂ) :
    ((a * d) * p) • f =
      (a : ℂ) * ((f * (p : ℂ)) * (d : ℂ)) := by sorry
