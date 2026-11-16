-- Prove2me | Theorems.Thm_Kyprianou_Ch01_lampertiCompoundPoissonToBranchingLawNonexplosive
-- name    : Kyprianou.Ch01.lampertiCompoundPoissonToBranchingLawNonexplosive
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T10:18:22.486693+00:00
-- url     : https://prove2.me/theorems/ac1b29c6-5525-4344-a03d-7469824736ed
-- title:
--   §1.3.4: reverse Lamperti law with explicit non-explosion, without offspring finite moment
-- statement:
--   Reverse Lamperti time-change for a compound-Poisson driver with skip-free negative jumps and arbitrary offspring law. Replaces the finite-mean assumption by an explicit pathwise non-explosion of the inverse-speed clock. Assumes the branching process is conservative through its PMF Markov semigroup and generator.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4 equations (1.18)–(1.19); subsequent Chapter 10 explosion discussion.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.lampertiCompoundPoissonToBranchingLawNonexplosive
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (law : PopulationLaws)
    (hbranch : HasBranchingProperty law)
    (hMarkov : IsPopulationMarkovSemigroup law)
    (hInitial : ∀ y : ℕ, law y 0 = PMF.pure y)
    (hRates : IsBranchingRateGenerator law rate offspring)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver
      arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k)
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation
            (integerCompoundPoisson y arrival marks) s ω) :
    ∀ (y : ℕ) (t : ℝ≥0) (k : ℕ),
      law y t k =
        Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat = k} := by
  sorry
