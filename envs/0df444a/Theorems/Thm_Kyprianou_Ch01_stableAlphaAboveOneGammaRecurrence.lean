-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneGammaRecurrence
-- name    : Kyprianou.Ch01.stableAlphaAboveOneGammaRecurrence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:20:06.430229+00:00
-- url     : https://prove2.me/theorems/7fdd8b75-fbba-4ece-986a-a51a85685754
-- title:
--   Gamma recurrence across the alpha above one stable Fourier regime
-- statement:
--   For 1<alpha<2, Γ(1−alpha)=−alpha Γ(−alpha). This is the exact non-pole Gamma functional recurrence needed when integrating the compensated α-stable Fourier kernel by parts to the already formalised alpha−1 deficit integral.
-- source:
--   Kyprianou (2006), Chapter 1 stable characteristic exponents; real Gamma functional equation in the α∈(1,2) regime.

import Mathlib
open Real Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaAboveOneGammaRecurrence
    (alpha : ℝ) (h1 : 1 < alpha) (h2 : alpha < 2) :
    Real.Gamma (1 - alpha) = -alpha * Real.Gamma (-alpha) := by
  sorry
