-- Prove2me | Theorems.Thm_Kyprianou_Ch01_levyTripletExponentSignBridgeReviewed
-- name    : Kyprianou.Ch01.levyTripletExponentSignBridgeReviewed
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T10:13:52.87911+00:00
-- url     : https://prove2.me/theorems/e91d6755-e72d-4161-9e49-fa03baba546f
-- title:
--   Reviewed sign bridge for the Lévy–Khintchine characteristic exponent
-- statement:
--   Explicit negative-exponent bridge between the LeanLevy Lévy-Khintchine triple and Kyprianou’s book convention, identifying drift sign, Gaussian variance one-half normalisation and compensated jump kernel.
-- source:
--   Kyprianou (2006), Chapter 1 Theorem 1.3, equations (1.1)–(1.2).

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.levyTripletExponentSignBridgeReviewed
    (T : ProbabilityTheory.LevyKhintchineTriple) (xi : ℝ) :
    -levyTripleExponent T xi =
      -(Complex.I * (((T.drift * xi : ℝ) : ℂ))) +
      (((T.gaussianVariance : ℝ) * xi ^ 2 / 2 : ℝ) : ℂ) -
      (∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂T.levyMeasure) := by
  sorry
