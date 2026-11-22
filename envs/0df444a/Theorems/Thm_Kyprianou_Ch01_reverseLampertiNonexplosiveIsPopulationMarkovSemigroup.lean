-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveIsPopulationMarkovSemigroup
-- name    : Kyprianou.Ch01.reverseLampertiNonexplosiveIsPopulationMarkovSemigroup
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T23:30:45.189198+00:00
-- url     : https://prove2.me/theorems/9a4f32df-f1b5-4d5d-94d2-593eda2122cb
-- title:
--   Nonexplosive inverse Lamperti time-changed population Markov semigroup
-- statement:
--   Show that the time-changed nonexplosive integer compound-Poisson population defines a genuine conservative population Markov semigroup in branching time, under the exactly stated driver, jump support, offspring and explicit nonexplosion assumptions. The required clock-shifted strong-Markov restart is a separate stochastic obligation from independent-ancestor convolution.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4, reverse Lamperti law with explicit non-explosion, equation (1.19)

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiNonexplosiveIsPopulationMarkovSemigroup
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
    IsPopulationMarkovSemigroup K := by
  sorry
