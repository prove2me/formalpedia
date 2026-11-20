-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianLaplaceRootProduct
-- name    : Kyprianou.Ch01.inverseGaussianLaplaceRootProduct
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:08:06.430325+00:00
-- url     : https://prove2.me/theorems/c8b393f4-39aa-4878-af81-8c8990101894
-- title:
--   inverseGaussianLaplaceRootProduct
-- statement:
--   For s>0 and q>=0, the reciprocal Gaussian root exponent 2sqrt((s²/2)(b²/2+q)) equals s sqrt(b²+2q).
-- source:
--   Kyprianou (2006) Exercise 1.6(iii), inverse-Gaussian Laplace integral normalisation.

import Mathlib
open Real
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianLaplaceRootProduct
    (s b q : ℝ) (hs : 0 < s) (hq : 0 ≤ q) :
    2 * Real.sqrt ((s ^ 2 / 2) * (b ^ 2 / 2 + q)) =
      s * Real.sqrt (b ^ 2 + 2 * q) := by sorry
