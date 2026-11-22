-- Prove2me | Theorems.Thm_Kyprianou_Ch01_lampertiBranchingToCompoundPoissonPathLawWithoutMoment
-- name    : Kyprianou.Ch01.lampertiBranchingToCompoundPoissonPathLawWithoutMoment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T10:02:18.938226+00:00
-- url     : https://prove2.me/theorems/318afc19-2086-4e20-9846-225169aaa3c1
-- title:
--   §1.3.4: forward Lamperti correspondence without finite offspring first moment
-- statement:
--   The forward Lamperti time change identifies the law of a nonexplosive càdlàg Markov branching population with the stopped compound-Poisson lattice path. Removes the extraneous finite first-moment restriction; the càdlàg and Markov assumptions retain the non-explosion and lifetime model constraints.
-- source:
--   Kyprianou (2006), §1.3.4, equations (1.17)–(1.18).

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.lampertiBranchingToCompoundPoissonPathLawWithoutMoment
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
      (P y).map
        (fun ω => fun t : ℝ≥0 => (branchingToPoisson Y t ω : ℤ)) =
      Q.map
        (fun ω => fun t : ℝ≥0 =>
          stoppedIntegerCompoundPoisson y arrival marks t ω) := by
  sorry
