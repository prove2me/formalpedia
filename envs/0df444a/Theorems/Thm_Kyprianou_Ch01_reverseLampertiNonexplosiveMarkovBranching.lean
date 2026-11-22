-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveMarkovBranching
-- name    : Kyprianou.Ch01.reverseLampertiNonexplosiveMarkovBranching
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T20:40:00.633486+00:00
-- url     : https://prove2.me/theorems/47018969-8054-4668-8d7b-b5a39c5713f7
-- title:
--   Reverse Lamperti time-changed lattice compound Poisson law is a branching Markov semigroup
-- statement:
--   Given an exact conservative law K for the inverse Lamperti time-change of an integer compound-Poisson random walk under explicit non-explosion, establish the branching convolution and time-homogeneous Markov semigroup identities. Use independent marked compound-Poisson increments, the inverse-speed occupation time-change and strong Markov at clock stopping times. This is the Markov/branching component of reverse Lamperti, separate from its fixed-time measurability and generator.
-- source:
--   Kyprianou Ch1 §1.3.4. Connected parent reverseLampertiNonexplosiveConstructsBranchingLaw add9a198-d73d-4166-b02f-7086a5eb80b0; original root ac1b29c6-5525-4344-a03d-7469824736ed.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiNonexplosiveMarkovBranching
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
    HasBranchingProperty K ∧ IsPopulationMarkovSemigroup K := by
  sorry
