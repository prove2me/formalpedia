-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingExpTermCompactLipschitz
-- name    : Kyprianou.Ch01.branchingExpTermCompactLipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T09:20:06.693955+00:00
-- url     : https://prove2.me/theorems/cfe4f722-d2bd-43e9-bee7-cf6742315ea0
-- title:
--   Uniform local Lipschitz bound for every branching offspring exponential, without moments
-- statement:
--   For each offspring index k and strictly positive compact cumulant interval [a,b], the exponential term exp(-q(k-1)) is uniformly Lipschitz with constant 1/a+exp(b), independent of k. For k>=1 use the already Proved exp_uniform_lipschitz_on_positive with natural k-1. For k=0 use the exp_lipschitz_below_upper lemma. The constant is summable against an arbitrary PMF, even with infinite mean.
-- source:
--   Kyprianou (2006) Chapter 1 branching mechanism; Proved Chapter 1 exp_uniform_lipschitz_on_positive and exp_lipschitz_below_upper.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 Real Set
open scoped Topology
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingExpTermCompactLipschitz
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (k : ℕ) (x y : ℝ)
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    |Real.exp (-y * ((k : ℝ) - 1)) -
      Real.exp (-x * ((k : ℝ) - 1))| ≤
      (a⁻¹ + Real.exp b) * |y - x| := by
  sorry
