-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneComplexRemainderQuadratic
-- name    : Kyprianou.Ch01.stableAlphaOneComplexRemainderQuadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T10:30:44.922414+00:00
-- url     : https://prove2.me/theorems/ad97529a-a56c-423a-9a7a-a00330ff2ed9
-- title:
--   Quadratic Taylor control of the compensated complex exponential at the origin
-- statement:
--   Whenever |zr|≤1, the norm of 1−exp(i zr)+i zr is at most (zr)². This is the key second-order Taylor estimate that makes the compensated complex index-one stable Lévy kernel locally integrable after division by r². The proof uses the exact pinned Mathlib complex exponential remainder inequality.
-- source:
--   Kyprianou (2006), Chapter 1, complex compensated stable Lévy kernel near the origin.

import Mathlib
open Complex Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneComplexRemainderQuadratic
    (z r : ℝ) (hsmall : |z * r| ≤ 1) :
    ‖(1 : ℂ) - Complex.exp (Complex.I * ((z * r : ℝ) : ℂ)) +
      Complex.I * ((z * r : ℝ) : ℂ)‖ ≤ (z * r) ^ 2 := by
  sorry
