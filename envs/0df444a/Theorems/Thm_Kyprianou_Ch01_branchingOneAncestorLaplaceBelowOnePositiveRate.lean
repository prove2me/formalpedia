-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorLaplaceBelowOnePositiveRate
-- name    : Kyprianou.Ch01.branchingOneAncestorLaplaceBelowOnePositiveRate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T07:56:39.435361+00:00
-- url     : https://prove2.me/theorems/03eb9c74-1436-4403-9f34-82769e0470f9
-- title:
--   Strictly subunit one-ancestor Laplace transform under a positive branching life rate
-- statement:
--   For a conservative countable-state Markov population semigroup with initial point mass at 1, strictly positive life rate, and the exact branching Q-derivatives, the one-ancestor probability of surviving in a positive state remains positive at every finite time. Consequently its Laplace transform is strictly less than 1 for every q>0. Establish survival via the semigroup law and positive small-time diagonal mass from the generator; no finite offspring mean is assumed.
-- source:
--   Kyprianou (2006), Ch 1 §1.3.4: exponential holding-time, one-ancestor survival and Laplace transform nondegeneracy.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingOneAncestorLaplaceBelowOnePositiveRate
    (rate : ℝ≥0) (hrate : 0 < rate) (offspring : PMF ℕ)
    (K : PopulationLaws)
    (hSemi : IsPopulationMarkovSemigroup K)
    (hInit : ∀ y : ℕ, K y 0 = PMF.pure y)
    (hGen : IsBranchingRateGenerator K rate offspring) :
    ∀ (t : ℝ≥0) (q : ℝ), 0 < q →
      branchingLaplace K 1 t q < 1 := by
  sorry
