-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorGeneratorFromRates
-- name    : Kyprianou.Ch01.branchingOneAncestorGeneratorFromRates
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T10:02:42.037195+00:00
-- url     : https://prove2.me/theorems/6a1c82e2-e5a3-4216-a634-3aa3c4298af1
-- title:
--   Exercise 1.11(iii): derive the one-ancestor Laplace generator from branching transition rates
-- statement:
--   Derive the t=0 derivative of the one-ancestor Laplace transform from the branching Q-matrix for exponential individual lifetime rate and offspring law, avoiding an assumed Laplace-generator identity.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.11(iii) and §1.3.4.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingOneAncestorGeneratorFromRates
    (law : PopulationLaws) (rate : ℝ≥0) (offspring : PMF ℕ)
    (hrate : 0 < rate) (hNoNullJumps : offspring 1 = 0)
    (hinit : law 1 0 = PMF.pure 1)
    (hRates : IsBranchingRateGenerator law rate offspring) :
    ∀ q : ℝ, 0 < q →
      HasDerivWithinAt
        (fun t : ℝ => branchingLaplace law 1 (Real.toNNReal t) q)
        (-(branchingMechanism (rate : ℝ) offspring q) * Real.exp (-q))
        (Set.Ici 0) 0 := by
  sorry
