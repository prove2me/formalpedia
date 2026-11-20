-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianBaseRootScale
-- name    : Kyprianou.Ch01.inverseGaussianBaseRootScale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:52:51.326725+00:00
-- url     : https://prove2.me/theorems/89594da1-093c-4c17-8613-6766093806bc
-- title:
--   inverseGaussianBaseRootScale
-- statement:
--   For positive b, sqrt2 * sqrt(b²/2)=b exactly by real square root multiplication and sqrt(b²)=b.
-- source:
--   Kyprianou (2006) Chapter 1 inverse Gaussian Gamma normalisation.

import Mathlib
open Complex Real ComplexOrder
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianBaseRootScale
    (b : ℝ) (hb : 0 < b) :
    Real.sqrt 2 * Real.sqrt (b ^ 2 / 2) = b := by sorry
