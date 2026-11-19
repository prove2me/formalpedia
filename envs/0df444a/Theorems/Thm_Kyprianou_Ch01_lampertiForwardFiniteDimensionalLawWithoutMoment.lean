-- Prove2me | Theorems.Thm_Kyprianou_Ch01_lampertiForwardFiniteDimensionalLawWithoutMoment
-- name    : Kyprianou.Ch01.lampertiForwardFiniteDimensionalLawWithoutMoment
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T12:45:08.453263+00:00
-- url     : https://prove2.me/theorems/45b13ab4-970c-4134-a679-c62b276b5f42
-- title:
--   Forward Lamperti law: finite-dimensional distributions under branching generator
-- statement:
--   For each initial population and every finite family of physical times, the vector of forward time-changed branching population values has the same joint distribution as the corresponding vector for the stopped compound Poisson process. Proving this requires generator/semigroup uniqueness beyond the already-Proved pathwise clock identities.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4 and (1.17)–(1.18); full original no-moment source-bound Lamperti path-law target 318afc19-2086-4e20-9846-225169aaa3c1.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.lampertiForwardFiniteDimensionalLawWithoutMoment
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (Y : ℝ≥0 → Ω → ℕ)
    (P : ℕ → Measure Ω) (law : PopulationLaws)
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hRate : 0 < rate)
    (offspring : PMF ℕ) (hNoNullJumps : offspring 1 = 0)
    (hBranching : HasBranchingProperty law)
    (hMarkov : IsPopulationMarkovPath Y P law)
    (hSemigroup : IsPopulationMarkovSemigroup law)
    (hGenerator : IsBranchingRateGenerator law rate offspring)
    (hInitial : ∀ y : ℕ, P y {ω | Y 0 ω = y} = 1)
    (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (hCadlag : ∀ y : ℕ, ∀ᵐ ω ∂P y,
      IsCadlag (fun t : ℝ≥0 => Y t ω))
    (arrival marks : ℕ → Ω' → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hDriver : IsCompoundPoissonDriver
      arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k) :
    ∀ y : ℕ, ∀ n : ℕ, ∀ times : Fin n → ℝ≥0,
      (P y).map
        (fun ω => fun i : Fin n =>
          (branchingToPoisson Y (times i) ω : ℤ)) =
      Q.map
        (fun ω => fun i : Fin n =>
          stoppedIntegerCompoundPoisson y arrival marks (times i) ω) := by
  sorry
