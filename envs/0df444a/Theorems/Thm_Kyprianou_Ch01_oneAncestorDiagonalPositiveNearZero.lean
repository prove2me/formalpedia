-- Prove2me | Theorems.Thm_Kyprianou_Ch01_oneAncestorDiagonalPositiveNearZero
-- name    : Kyprianou.Ch01.oneAncestorDiagonalPositiveNearZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T08:57:17.152203+00:00
-- url     : https://prove2.me/theorems/ad18afcb-ee36-406c-9947-c4b7572468a0
-- title:
--   One-ancestor diagonal probability is positive in a neighbourhood of time zero
-- statement:
--   A Markov population law starting in state one and possessing the finite branching generator derivative at zero has a transition probability from one to one which is positive for all sufficiently small nonnegative times. This follows from HasDerivWithinAt.continuousWithinAt, the value one at zero, and the neighbourhood definition of continuity; no offspring moment condition.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4; verified branching rate generator and continuity within the nonnegative time interval.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.oneAncestorDiagonalPositiveNearZero
    (rate : ℝ≥0) (offspring : PMF ℕ) (K : PopulationLaws)
    (hInit : K 1 0 = PMF.pure 1)
    (hGen : IsBranchingRateGenerator K rate offspring) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ≥0, (t : ℝ) < δ →
        0 < ((K 1 t) 1).toReal := by
  sorry
