-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingU_zero
-- name    : Kyprianou.Ch01.branchingU_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:38:20.686885+00:00
-- url     : https://prove2.me/theorems/14b4b132-cd33-49f5-aa78-3e8517c1804f
-- title:
--   Branching cumulant starts from the identity at time zero
-- statement:
--   For a Markov branching population whose time-zero distribution from y ancestors is the pure mass at y, the logarithmic one-ancestor Laplace cumulant equals the initial parameter q at time zero.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.11(iii), original branchingLaplaceEvolution theorem e3e56c90-ad7f-4e20-9c86-ac6cc59168cd.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingU_zero
    (law : PopulationLaws)
    (hinit : ∀ y : ℕ, law y 0 = PMF.pure y)
    (q : ℝ) :
    branchingU law 0 q = q := by sorry
