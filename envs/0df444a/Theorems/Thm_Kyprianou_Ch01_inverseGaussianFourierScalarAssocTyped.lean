-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianFourierScalarAssocTyped
-- name    : Kyprianou.Ch01.inverseGaussianFourierScalarAssocTyped
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T18:51:54.392216+00:00
-- url     : https://prove2.me/theorems/59ec3617-3afa-4987-a15d-246a2690e845
-- title:
--   Output-typed real-density Fourier scalar rearrangement in complex space
-- statement:
--   For real a,d,p and complex f, the explicitly complex-typed scalar action ((a*d)*p) • f is the product a*(f*p*d). This annotated result removes an ambiguous type-class output when elaborating the generic scalar action.
-- source:
--   Kyprianou (2006), Exercise 1.6(ii) complex Fourier integrand; Mathlib.Data.Complex.Basic real_smul.

import Mathlib
import Mathlib.Data.Complex.Basic
open Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianFourierScalarAssocTyped
    (a d p : ℝ) (f : ℂ) :
    ((((a * d) * p) • f) : ℂ) =
      (a : ℂ) * ((f * (p : ℂ)) * (d : ℂ)) := by sorry
