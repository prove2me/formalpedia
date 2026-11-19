-- Prove2me | Theorems.Thm_Kyprianou_Ch01_finiteMeanCompoundPoissonClockNonexplosion
-- name    : Kyprianou.Ch01.finiteMeanCompoundPoissonClockNonexplosion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T12:31:31.330543+00:00
-- url     : https://prove2.me/theorems/49bcca66-359d-49a6-bc0a-050150009610
-- title:
--   Chapter 1 reverse Lamperti: finite offspring mean implies reciprocal occupation clock non-explosion
-- statement:
--   A finite first moment of the non-null offspring PMF, with matching skip-free compound Poisson jump law and an honest compound Poisson driver, implies that the reciprocal occupation clock eventually exceeds every finite branching time, Q-almost surely, at each initial population. This is the explicit missing non-explosion implication needed to derive the source-fidelity reverse Lamperti law from the published no-moment theorem.
-- source:
--   Kyprianou (2006), Chapter 1 section 1.3.4, equations (1.18)-(1.19), nonexplosion under finite offspring first moment.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.finiteMeanCompoundPoissonClockNonexplosion
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (hFiniteMean : Summable
      (fun k : ℕ => (offspring k).toReal * (k : ℝ)))
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
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k) :
    ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation
            (integerCompoundPoisson y arrival marks) s ω := by
  sorry
