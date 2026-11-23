-- Prove2me | Theorems.Thm_Kyprianou_Ch01_zeroRateBranchingSemigroupUnique
-- name    : Kyprianou.Ch01.zeroRateBranchingSemigroupUnique
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T07:46:51.550667+00:00
-- url     : https://prove2.me/theorems/ab4b4c87-1dcb-43ad-a27b-e6786a7223c3
-- title:
--   Uniqueness of the conservative zero-rate branching transition semigroup
-- statement:
--   If two population Markov semigroups start at their state and their branching Q-generator is zero, then their transition PMFs agree at every time. At zero rate the y-scaled branching Q-matrix agrees exactly with the already Proved lattice-generator Q-matrix. Reuse Kyprianou.Ch01.lampertiLatticeGeneratorSemigroupUnique without adding explosion/moment restrictions.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4, zero-rate subcase of branching semigroup uniqueness; proof reuse from Kyprianou.Ch01.lampertiLatticeGeneratorSemigroupUnique.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.zeroRateBranchingSemigroupUnique
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (K₁ K₂ : PopulationLaws)
    (hSemi₁ : IsPopulationMarkovSemigroup K₁)
    (hSemi₂ : IsPopulationMarkovSemigroup K₂)
    (hInit₁ : ∀ y : ℕ, K₁ y 0 = PMF.pure y)
    (hInit₂ : ∀ y : ℕ, K₂ y 0 = PMF.pure y)
    (hGen₁ : IsBranchingRateGenerator K₁ 0 offspring)
    (hGen₂ : IsBranchingRateGenerator K₂ 0 offspring) :
    K₁ = K₂ := by
  sorry
