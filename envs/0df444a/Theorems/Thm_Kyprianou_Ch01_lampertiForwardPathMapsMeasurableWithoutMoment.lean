-- Prove2me | Theorems.Thm_Kyprianou_Ch01_lampertiForwardPathMapsMeasurableWithoutMoment
-- name    : Kyprianou.Ch01.lampertiForwardPathMapsMeasurableWithoutMoment
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T12:45:08.504206+00:00
-- url     : https://prove2.me/theorems/c79965ce-c470-48ca-a8ce-26e523ad6e21
-- title:
--   Forward Lamperti law: path-space measurability for transformed branching and Poisson processes
-- statement:
--   For each initial population the two path-valued random variables into the product measurable space of NNReal-indexed integers are measurable. This is a genuine separate hypothesis required to identify the full path-space pushforward probability measures from finite-dimensional distributions.
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

theorem Kyprianou.Ch01.lampertiForwardPathMapsMeasurableWithoutMoment
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
    ∀ y : ℕ,
      Measurable
        (fun ω : Ω => fun t : ℝ≥0 =>
          (branchingToPoisson Y t ω : ℤ)) ∧
      Measurable
        (fun ω : Ω' => fun t : ℝ≥0 =>
          stoppedIntegerCompoundPoisson y arrival marks t ω) := by
  sorry
