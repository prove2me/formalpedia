-- Prove2me | Theorems.Thm_OAI_binary_sweep_contraction_and_mixing
-- name    : OAI.binary_sweep_contraction_and_mixing
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:40.663126+00:00
-- url     : https://prove2.me/theorems/eb14e641-577b-4f56-8600-e221e9cab90a
-- statement:
--   The theorem states a conjunction of three facts about random binary coordinate sweeps. Here a deck of dimension d has positions Fin d → Bool (the vertices of the d-cube), and a sweep is a permutation of these positions built from independent fair coins: for each coordinate j and each assignment of the other d−1 coordinates, one coin decides whether to flip coordinate j at that assignment, and the d resulting coordinate layers are composed in increasing coordinate order. binaryLaw(d) is the law of this permutation over uniformly random coins. First, there is a constant g>0 and a dimension d₀ such that for all d ≥ d₀, every irreducible unitary complex representation ρ of the permutation group of the positions, of any dimension D, satisfies that the operator norm of the averaged operator Σ_g binaryLaw(d)(g) ρ(g) is at most D^(−g). Second, for every d>0, the expected sign of the random sweep is zero, that is, Σ_g binaryLaw(d)(g)·sign(g) = 0, with sign taken as ±1 in the reals. Third, there is a single number w of sweeps such that for every ε>0 there is d₀ with the following property for all d ≥ d₀ and every deterministic permutation τ: the total variation distance (half the sum of absolute mass differences) between the uniform law on all permutations and the law of g·τ⁻¹, where g is the product of w independent sweeps (the w-fold convolution power of binaryLaw(d)), is at most ε.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BinarySweep.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BinarySweep.lean; bytes 3386..3720
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_BinarySweep

namespace OAI

open scoped BigOperators

theorem binary_sweep_contraction_and_mixing :
    BinaryCoordinateSweeps.BinaryContractionTarget ∧
    (∀ d : ℕ, 0 < d → ∑ g : Equiv.Perm (BinaryCoordinateSweeps.Slot d),
      BinaryCoordinateSweeps.binaryLaw d g * BinaryCoordinateSweeps.realSign g = 0) ∧
    BinaryCoordinateSweeps.UniformSweepMixingTarget := by
  sorry

end OAI
