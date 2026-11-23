-- Prove2me | Theorems.Thm_Kyprianou_Ch01_pmfNatLaplaceDifferenceHasSumZero
-- name    : Kyprianou.Ch01.pmfNatLaplaceDifferenceHasSumZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T07:31:43.938034+00:00
-- url     : https://prove2.me/theorems/f1d9c889-b1b7-4bff-836c-370f025f2c6c
-- title:
--   Equality of discrete Laplace transforms gives zero-sum real power-series coefficient differences at positive arguments
-- statement:
--   For PMFs p and r on nonnegative integers with equal real exponential Laplace transforms for all positive q, put q=−log z for 0<z≤1/2. Then exp(−q n)=z^n, so their real weighted PGFs agree on this interval. Both weighted series are summable by domination using the PMF total mass. Subtracting their HasSum witnesses yields HasSum (z^n(p_n−r_n)) 0. No moment assumptions.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4, discrete generating-function uniqueness; real log/exponential change of variables

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.pmfNatLaplaceDifferenceHasSumZero
    (p r : PMF ℕ)
    (hLaplace : ∀ (q : ℝ), 0 < q →
      (∑' n : ℕ, (p n).toReal * Real.exp (-q * (n : ℝ))) =
      (∑' n : ℕ, (r n).toReal * Real.exp (-q * (n : ℝ)))) :
    ∀ z : ℝ, 0 < z → z ≤ (1/2 : ℝ) →
      HasSum (fun n : ℕ =>
        z ^ n * ((p n).toReal - (r n).toReal)) 0 := by
  sorry
