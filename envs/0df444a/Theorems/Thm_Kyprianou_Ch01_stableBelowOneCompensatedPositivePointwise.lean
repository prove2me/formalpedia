-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableBelowOneCompensatedPositivePointwise
-- name    : Kyprianou.Ch01.stableBelowOneCompensatedPositivePointwise
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T20:35:42.565172+00:00
-- url     : https://prove2.me/theorems/87d4ecff-5865-41e0-a751-68c36d4d2247
-- title:
--   Original compensated stable positive Fourier kernel pointwise algebra
-- statement:
--   For positive jump radius r, the stable weighted original levyCompensatedIntegrand is the weighted untruncated Fourier deficit minus the source small-jump cutoff term i c xi r^-alpha when r<1, with zero cutoff term otherwise. Identity follows from r^(-alpha-1)*r=r^-alpha and exact source compensator definition.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.4, compensated two-sided stable density.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_ProbabilityTheory_levyCompensatedIntegrand_def
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Complex Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableBelowOneCompensatedPositivePointwise
    (alpha c xi r : ℝ) (hr : 0 < r) :
    (c * r ^ (-alpha - 1)) •
      ProbabilityTheory.levyCompensatedIntegrand xi r =
      (c : ℂ) *
        ((Complex.exp ((Complex.I * (xi : ℂ)) * (r : ℂ)) - 1) *
          (((r ^ (-alpha - 1) : ℝ) : ℂ))) -
      (Complex.I * ((c * xi : ℝ) : ℂ)) *
        (if r < 1 then (((r ^ (-alpha) : ℝ) : ℂ)) else 0) := by sorry
