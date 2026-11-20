-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaBelowOneGammaRecurrence
-- name    : Kyprianou.Ch01.stableAlphaBelowOneGammaRecurrence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:28:03.991036+00:00
-- url     : https://prove2.me/theorems/f39fd488-8446-4468-80bd-2a9e982f039c
-- title:
--   Stable index below one Gamma recurrence across zero without a pole
-- statement:
--   For stable index 0<alpha<1, Γ(1−alpha)=−alpha Γ(−alpha), using the true real Gamma functional equation at nonzero negative noninteger argument −alpha. This is the exact coefficient conversion when integrating by parts the real negative-Laplace stable Gamma deficit integral at w=−1.
-- source:
--   Kyprianou (2006), Chapter 1 stable α∈(0,1) Fourier characteristic exponent, Gamma recurrence.

import Mathlib
open Real Complex MeasureTheory Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaBelowOneGammaRecurrence
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1) :
    Real.Gamma (1 - alpha) = (-alpha) * Real.Gamma (-alpha) := by
  sorry
