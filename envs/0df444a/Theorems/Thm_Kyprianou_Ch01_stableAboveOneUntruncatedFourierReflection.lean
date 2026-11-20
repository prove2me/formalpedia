-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAboveOneUntruncatedFourierReflection
-- name    : Kyprianou.Ch01.stableAboveOneUntruncatedFourierReflection
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:20:57.127829+00:00
-- url     : https://prove2.me/theorems/71701952-4c70-42e6-907d-d0418a2953ff
-- title:
--   Reflection of the stable untruncated Fourier kernel through complex conjugation
-- statement:
--   At any real frequency xi and real stable index alpha, the positive halfline integral of the untruncated compensated Fourier kernel at -xi is the complex conjugate of the integral at xi. The denominator is real, and conjugation sends e^(i xi r) to e^(-i xi r). This is independent of integrability hypotheses through Bochner integral convention.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4, real Lévy measure Fourier conjugate symmetry.

import Mathlib
open MeasureTheory Set Real Complex
open scoped ComplexConjugate
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAboveOneUntruncatedFourierReflection
    (alpha xi : ℝ) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (Complex.I * (((-xi * r : ℝ) : ℂ))) - 1 -
        Complex.I * (((-xi * r : ℝ) : ℂ))) /
        (((r ^ (alpha + 1) : ℝ) : ℂ)) ∂volume) =
      conj
        (∫ r in Set.Ioi (0 : ℝ),
          (Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) - 1 -
            Complex.I * (((xi * r : ℝ) : ℂ))) /
            (((r ^ (alpha + 1) : ℝ) : ℂ)) ∂volume) := by sorry
