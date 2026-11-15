-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingU_derivativeAtZero
-- name    : Kyprianou.Ch01.branchingU_derivativeAtZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:41:36.291209+00:00
-- url     : https://prove2.me/theorems/f50f28d1-1ca2-4437-9625-2983814522a5
-- title:
--   Kyprianou branching cumulant: right derivative at time zero is the branching mechanism
-- statement:
--   For a branching process with the prescribed pure time-zero law and one-particle Laplace generator, the right derivative of its negative logarithmic Laplace cumulant at time zero equals the branching mechanism. This is the initial derivative case of Chapter 1 Exercise 1.11(iii).
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.11(iii), source theorem e3e56c90-ad7f-4e20-9c86-ac6cc59168cd.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingU_derivativeAtZero
    (law : PopulationLaws)
    (rate : ℝ) (offspring : PMF ℕ)
    (hinit : ∀ y : ℕ, law y 0 = PMF.pure y)
    (hgenerator : ∀ q : ℝ, 0 < q →
      HasDerivWithinAt
        (fun t : ℝ =>
          branchingLaplace law 1 (Real.toNNReal t) q)
        (-(branchingMechanism rate offspring q) * Real.exp (-q))
        (Set.Ici 0) 0)
    (q : ℝ) (hq : 0 < q) :
    HasDerivWithinAt
      (fun t : ℝ => branchingU law (Real.toNNReal t) q)
      (branchingMechanism rate offspring q)
      (Set.Ici 0) 0 := by sorry
