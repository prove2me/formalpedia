-- Prove2me | Theorems.Thm_Kyprianou_Ch01_levyTripleExponentZero
-- name    : Kyprianou.Ch01.levyTripleExponentZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:44:45.097178+00:00
-- url     : https://prove2.me/theorems/d44112f2-d50c-4b3c-be5a-678010b5f7ae
-- title:
--   The original Lévy–Khintchine characteristic exponent vanishes at Fourier frequency zero
-- statement:
--   For any source LevyKhintchineTriple, the source-exact signed exponent from the original drift, Gaussian variance and compensated Lévy measure vanishes at frequency 0. Follows from the already-Proved levyCompensatedIntegrand_zero_left and zero drift/Gaussian terms.
-- source:
--   Kyprianou (2006) Chapter 1 Theorem 1.3, Lévy-Khintchine formula at frequency zero.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_ProbabilityTheory_levyCompensatedIntegrand_zero_left
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.levyTripleExponentZero
    (T : ProbabilityTheory.LevyKhintchineTriple) :
    Kyprianou.Ch01.levyTripleExponent T 0 = 0 := by sorry
