-- Prove2me | Theorems.Thm_Kyprianou_Ch01_expNegLogNatPow
-- name    : Kyprianou.Ch01.expNegLogNatPow
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T07:37:00.410331+00:00
-- url     : https://prove2.me/theorems/3a3d75c4-5211-4e29-8b20-b326e0c58346
-- title:
--   Exponential Laplace weights equal powers at the negative logarithm of a positive argument
-- statement:
--   For z>0 and natural n, exp(−(−log z) n)=z^n, by Real.exp_nat_mul and Real.exp_log. This is the exact change of variables connecting Laplace transforms with discrete generating functions.
-- source:
--   Kyprianou (2006) Chapter 1 branching population PGFs and elementary real log/exponential identity.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.expNegLogNatPow
    (z : ℝ) (hz : 0 < z) (n : ℕ) :
    Real.exp (-(-Real.log z) * (n : ℝ)) = z ^ n := by
  sorry
