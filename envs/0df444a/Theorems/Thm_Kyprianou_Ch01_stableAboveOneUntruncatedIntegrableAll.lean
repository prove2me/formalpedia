-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAboveOneUntruncatedIntegrableAll
-- name    : Kyprianou.Ch01.stableAboveOneUntruncatedIntegrableAll
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T23:54:14.020504+00:00
-- url     : https://prove2.me/theorems/211b9920-02bf-42fa-8130-24c0f4f4d3b8
-- title:
--   Complex integrability of the original above-one untruncated compensated Fourier kernel at all real frequencies
-- statement:
--   For 1<alpha<2, the source untruncated stable compensated Fourier kernel is integrable on the positive halfline at all real frequencies: positive xi by scaling from proved unit-frequency integrability, negative xi by conjugation, and zero frequency trivially.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4, compensated Fourier kernel and source Lévy measure.

import Mathlib
open MeasureTheory Set Real Complex
open scoped ComplexConjugate
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAboveOneUntruncatedIntegrableAll
    (alpha xi : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    IntegrableOn
      (fun r : ℝ =>
        (Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) - 1 -
          Complex.I * (((xi * r : ℝ) : ℂ))) /
          (((r ^ (alpha + 1) : ℝ) : ℂ)))
      (Set.Ioi (0 : ℝ)) := by sorry
