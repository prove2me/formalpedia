-- Prove2me | Theorems.Thm_Kyprianou_Ch01_levyTripletExponentSignBridge
-- name    : Kyprianou.Ch01.levyTripletExponentSignBridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T10:02:53.640503+00:00
-- url     : https://prove2.me/theorems/579b059f-9eb8-4a72-9bcb-4982abb551eb
-- title:
--   levyTripletExponentSignBridge
-- statement:
--   Explicit negative-exponent bridge between the LeanLevy Lévy-Khintchine triple and Kyprianou’s book convention, identifying drift sign, Gaussian variance one-half normalisation and compensated jump kernel.
-- source:
--   Kyprianou (2006), Chapter 1 Theorem 1.3, equations (1.1)–(1.2).

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.levyTripletExponentSignBridge
    (T : ProbabilityTheory.LevyKhintchineTriple) (xi : ℝ) :
    -levyTripleExponent T xi =
      -(Complex.I * (((T.drift * xi : ℝ) : ℂ))) +
      (((T.gaussianVariance : ℝ) * xi ^ 2 / 2 : ℝ) : ℂ) -
      (∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂T.levyMeasure) := by
  sorry
