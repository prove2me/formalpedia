-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianLaplacePrefactor
-- name    : Kyprianou.Ch01.inverseGaussianLaplacePrefactor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:08:06.753247+00:00
-- url     : https://prove2.me/theorems/ae148d9f-d75c-41b2-8621-fbc41c105acf
-- title:
--   inverseGaussianLaplacePrefactor
-- statement:
--   For positive barrier s, the inverse-Gaussian density normaliser times the reciprocal Gaussian integral coefficient equals exactly one.
-- source:
--   Kyprianou (2006) Exercise 1.6(iii), inverse-Gaussian Laplace integral normalisation.

import Mathlib
open Real
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianLaplacePrefactor
    (s : ℝ) (hs : 0 < s) :
    (s / Real.sqrt (2 * Real.pi)) *
      (Real.sqrt Real.pi / Real.sqrt (s ^ 2 / 2)) = 1 := by sorry
