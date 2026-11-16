-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanPhiPositive
-- name    : Kyprianou.Ch01.mckeanPhiPositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:46:27.711387+00:00
-- url     : https://prove2.me/theorems/12d7d9c8-f72f-4593-845c-585c7cf7931c
-- title:
--   Exercise 1.10: the McKean Brownian lower-passage parameter is positive
-- statement:
--   For positive Brownian volatility and discount parameter, the positive root phi=(sqrt(gamma^2+2*sigma^2*q)+gamma)/sigma^2 appearing in McKean Brownian optimal stopping is strictly positive for arbitrary real drift gamma.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.10, scalar positive-root component of Kyprianou.Ch01.mckeanBrownianPutOptimal.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open Kyprianou.Ch01 MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanPhiPositive
    (sigma gamma q : ℝ) (hsigma : 0 < sigma) (hq : 0 < q) :
    0 < (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) /
      sigma ^ 2 := by sorry
