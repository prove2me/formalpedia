-- Prove2me | Theorems.Thm_Kyprianou_Ch01_positiveOneAncestorDiagonalMassAtFiniteTime
-- name    : Kyprianou.Ch01.positiveOneAncestorDiagonalMassAtFiniteTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T07:59:31.301857+00:00
-- url     : https://prove2.me/theorems/a2bb7a79-18b7-46f8-83ae-cdd53a6f07ac
-- title:
--   One-ancestor diagonal transition probability remains positive at every finite time
-- statement:
--   For a conservative population Markov semigroup initially at state 1 with finite branching Q-diagonal derivative −rate, the transition probability K(1,t;1) is strictly positive for every finite t. Generator regularity makes this probability close to one for short times. Chapman-Kolmogorov gives K(1,s+t;1)≥K(1,s;1)K(1,t;1); time subdivision then yields positivity at every finite horizon. This remains valid for offspring distributions with infinite mean.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4, first-event exponential holding and semigroup multiplication, no finite offspring moment.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.positiveOneAncestorDiagonalMassAtFiniteTime
    (rate : ℝ≥0) (hrate : 0 < rate) (offspring : PMF ℕ)
    (K : PopulationLaws)
    (hSemi : IsPopulationMarkovSemigroup K)
    (hInit : ∀ y : ℕ, K y 0 = PMF.pure y)
    (hGen : IsBranchingRateGenerator K rate offspring) :
    ∀ t : ℝ≥0, 0 < ((K 1 t) 1).toReal := by
  sorry
