-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneImaginaryFrequencySubstitution
-- name    : Kyprianou.Ch01.stableAlphaOneImaginaryFrequencySubstitution
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T10:49:57.477382+00:00
-- url     : https://prove2.me/theorems/f83bdbb5-f699-404c-a528-7221fbb212a1
-- title:
--   Exact positive-frequency substitution for the imaginary stable alpha-one phase integral
-- statement:
--   For any positive frequency z, the compensated sine phase integral with fixed cutoff r<1 transforms under u=zr into z times the same sine kernel with frequency-free argument and the shifted cutoff u<z. This is the key change of variables causing the log(z) term in the alpha-one stable Lévy characteristic exponent.
-- source:
--   Kyprianou (2006), Chapter 1, alpha-one stable imaginary logarithmic phase.

import Mathlib
open MeasureTheory Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneImaginaryFrequencySubstitution
    (z : ℝ) (hz : 0 < z) :
    (∫ r in Set.Ioi (0 : ℝ),
      ((z * r) * (if r < 1 then (1 : ℝ) else 0) - Real.sin (z * r)) / r ^ 2 ∂volume) =
      z * (∫ u in Set.Ioi (0 : ℝ),
        (u * (if u < z then (1 : ℝ) else 0) - Real.sin u) / u ^ 2 ∂volume) := by
  sorry
