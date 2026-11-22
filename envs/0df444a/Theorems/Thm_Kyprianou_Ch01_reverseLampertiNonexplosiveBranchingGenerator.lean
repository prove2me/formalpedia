-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveBranchingGenerator
-- name    : Kyprianou.Ch01.reverseLampertiNonexplosiveBranchingGenerator
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T20:40:06.235832+00:00
-- url     : https://prove2.me/theorems/0ebe561e-7e7e-4e54-94dc-0b50c520c91e
-- title:
--   Reverse Lamperti time change has the continuous-time Markov branching generator
-- statement:
--   Given exact reverse Lamperti inverse-time-changed compound Poisson transition probabilities with the specified offspring jump law and global reciprocal-clock non-explosion, prove their right derivative at zero is the branching Q-matrix: diagonal -rate*y, off-diagonal rate*y*offspring(k+1-y), with p_1=0. Derive the first-event exponential waiting rate for initial population y and show probability of two or more events is o(t) without assuming an offspring moment. Handle absorbing zero state and nearest-downward-jump support.
-- source:
--   Kyprianou Ch1 §1.3.4 generator. Existing proved branchingTwoJumpsLittleO d82991e4-a21b-40b7-b7e9-edc934278997 and branchingOffDiagonalPointwiseSlope 18433076-d6b3-4f18-8180-31ec3663934d. Connected parent add9a198-d73d-4166-b02f-7086a5eb80b0; root ac1b29c6-5525-4344-a03d-7469824736ed.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiNonexplosiveBranchingGenerator
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k)
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω)
    (K : PopulationLaws)
    (hRealisation : ∀ (y : ℕ) (t : ℝ≥0) (k : ℕ),
      K y t k =
        Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat = k}) :
    IsBranchingRateGenerator K rate offspring := by
  sorry
