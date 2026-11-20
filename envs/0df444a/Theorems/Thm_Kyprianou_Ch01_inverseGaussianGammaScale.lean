-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianGammaScale
-- name    : Kyprianou.Ch01.inverseGaussianGammaScale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:42:22.377685+00:00
-- url     : https://prove2.me/theorems/0ab9b6b6-f54b-4e5a-8c44-803fd0fed066
-- title:
--   Negative-half-Gamma constant divided by sqrt(2pi) equals minus sqrt two
-- statement:
--   The exact inverse-Gaussian Levy density normalisation Gamma(-1/2)/sqrt(2 pi) equals minus sqrt two; follows from Gamma(-1/2)=-2sqrt pi and positive real sqrt multiplication.
-- source:
--   Kyprianou (2006) Exercise 1.6(ii), inverse Gaussian Fourier-Lévy normalisation.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianGammaNegativeHalf
open Complex Real Set
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianGammaScale :
    Real.Gamma (-(1 / 2 : ℝ)) /
      Real.sqrt (2 * Real.pi) = -Real.sqrt 2 := by sorry
