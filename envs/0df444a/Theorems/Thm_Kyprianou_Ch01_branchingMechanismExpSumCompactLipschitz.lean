-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingMechanismExpSumCompactLipschitz
-- name    : Kyprianou.Ch01.branchingMechanismExpSumCompactLipschitz
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T09:27:39.029817+00:00
-- url     : https://prove2.me/theorems/bb30427b-9038-4b6e-91c9-3f6d8cc44818
-- title:
--   Uniform positive-compact Lipschitz bound for unscaled branching offspring mechanism series
-- statement:
--   On strictly positive [a,b], an arbitrary offspring PMF's unscaled branching exponential sum is Lipschitz with constant a^-1+exp(b). The already Proved branchingExpTermCompactLipschitz bounds each summand by this common constant times p_k; the summability of both endpoint series and the fact that total PMF mass is one enable tsum_of_norm_bounded. Does not require finite offspring moment.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingMechanismExpSumCompactLipschitz
    (offspring : PMF ℕ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (x y : ℝ) (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    |(∑' k : ℕ, (offspring k).toReal *
       (1 - Real.exp (-y * ((k : ℝ) - 1)))) -
      (∑' k : ℕ, (offspring k).toReal *
       (1 - Real.exp (-x * ((k : ℝ) - 1))))| ≤
    (a⁻¹ + Real.exp b) * |y - x| := by
  sorry
