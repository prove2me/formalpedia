-- Prove2me | Theorems.Thm_Kyprianou_Ch01_geometricFourierTsum
-- name    : Kyprianou.Ch01.geometricFourierTsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T07:31:30.591205+00:00
-- url     : https://prove2.me/theorems/3a276037-d2fb-436e-be85-48d8d964183e
-- title:
--   Absolutely convergent geometric Fourier mixture formula on the unit disc
-- statement:
--   For 0<p<1 and a complex z of modulus at most one, the absolutely convergent geometric series Σ_{n≥0}p((1−p)z)^n equals p/(1−(1−p)z). This is the exact Fourier-series summation required when conditioning a geometrically stopped IID sum on the independent stopping count in Kyprianou Chapter 1 Exercise 1.2(ii).
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(ii), geometric mixture of fixed-count characteristic functions.

import Mathlib
open Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.geometricFourierTsum
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    (∑' n : ℕ,
      (p : ℂ) * ((((1 - p : ℝ) : ℂ) * z) ^ n)) =
      (p : ℂ) / (1 - (((1 - p : ℝ) : ℂ) * z)) := by
  sorry
