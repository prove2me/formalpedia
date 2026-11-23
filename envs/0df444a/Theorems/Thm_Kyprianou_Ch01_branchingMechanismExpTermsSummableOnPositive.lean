-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingMechanismExpTermsSummableOnPositive
-- name    : Kyprianou.Ch01.branchingMechanismExpTermsSummableOnPositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T09:27:34.137868+00:00
-- url     : https://prove2.me/theorems/df27f532-47aa-4d96-8fb4-897ae2f12f16
-- title:
--   Absolute summability of branching exponential mechanism terms for positive cumulant
-- statement:
--   For an arbitrary offspring PMF, a positive cumulant z in [a,b] with a>0 gives an absolutely summable real series of p_k times (1-exp(-z(k-1))). Dominate its absolute values by (1+exp(b))*p_k using the already Proved branchingMechanism_expUniformBound. No finite offspring mean.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingMechanismExpTermsSummableOnPositive
    (offspring : PMF ℕ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (z : ℝ) (hz : z ∈ Set.Icc a b) :
    Summable (fun k : ℕ => (offspring k).toReal *
      (1 - Real.exp (-z * ((k : ℝ) - 1)))) := by
  sorry
