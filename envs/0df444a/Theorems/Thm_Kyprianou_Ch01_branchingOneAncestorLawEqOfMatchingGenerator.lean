-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorLawEqOfMatchingGenerator
-- name    : Kyprianou.Ch01.branchingOneAncestorLawEqOfMatchingGenerator
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T20:36:25.608816+00:00
-- url     : https://prove2.me/theorems/0b3b4305-e152-40f3-8259-12fc68e5182b
-- title:
--   Uniqueness of the one-ancestor branching transition probabilities with identical conservative generators
-- statement:
--   For two conservative PMF-valued Markov branching semigroups, prove the distributions from one ancestor equal whenever the generators and offspring probability mass functions match, with no first moment assumption. Derive the same locally Lipschitz scalar equation for the one-ancestor generating function at each argument inside (0,1), using existing Proved branchingLaplaceEvolution and generator identities; use ODE uniqueness and uniqueness of the PGF to identify distributions. This is the substantial analytic child of reverse Lamperti semigroup uniqueness.
-- source:
--   Kyprianou Ch1 §1.3.4. Existing proved branchingLaplaceEvolution e3e56c90-ad7f-4e20-9c86-ac6cc59168cd, branchingOneAncestorInfiniteDerivative 6d9a6197-5ac3-4746-9c2a-cba76b1ce728. Parent uniqueness theorem abf1b453-26bc-421b-b350-3ce810bb8479, root ac1b29c6-5525-4344-a03d-7469824736ed.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingOneAncestorLawEqOfMatchingGenerator
    (rate : ℝ≥0) (offspring : PMF ℕ)
    (hNoZeroJumps : offspring 1 = 0)
    (K₁ K₂ : PopulationLaws)
    (hBranch₁ : HasBranchingProperty K₁)
    (hBranch₂ : HasBranchingProperty K₂)
    (hSemi₁ : IsPopulationMarkovSemigroup K₁)
    (hSemi₂ : IsPopulationMarkovSemigroup K₂)
    (hInit₁ : ∀ y : ℕ, K₁ y 0 = PMF.pure y)
    (hInit₂ : ∀ y : ℕ, K₂ y 0 = PMF.pure y)
    (hGen₁ : IsBranchingRateGenerator K₁ rate offspring)
    (hGen₂ : IsBranchingRateGenerator K₂ rate offspring) :
    ∀ t : ℝ≥0, K₁ 1 t = K₂ 1 t := by
  sorry
