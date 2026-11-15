-- Prove2me | Theorems.Thm_Kyprianou_Ch01_lampertiBranchingToCompoundPoissonPathLaw
-- name    : Kyprianou.Ch01.lampertiBranchingToCompoundPoissonPathLaw
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T08:16:58.342811+00:00
-- url     : https://prove2.me/theorems/25e34ee7-8362-4fbd-84aa-0418ac176b14
-- title:
--   §1.3.4, equations (1.17)–(1.18): forward Lamperti correspondence in full path law
-- statement:
--   Kyprianou (2006), Chapter 1 p. 25, equation (1.17) and jump law (1.18): for every finite integer initial population y, apply the right-inverse of integrated population occupation to an honest continuous-time Markov branching process. The resulting entire path, absorbed at extinction, has the law of a compound Poisson process of arrival rate λ with IID offspring-minus-one lattice jumps, stopped upon hitting zero. The premise expresses time-homogeneous Markov transition laws, generator rates λyp_(k+1−y), path càdlàg regularity, finite offspring mean for non-explosion, and independent exponential Poisson interarrivals and marks for the comparison law. The path distribution equality is the theorem conclusion, not an assumption. This is a strong unproved draft, subject to remote elaboration and source audit.
-- source:
--   Kyprianou, Introductory Lectures on Fluctuations of Lévy Processes with Applications (2006), Chapter 1 §1.3.4, printed pp. 24–26, (1.17), (1.18).

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.lampertiBranchingToCompoundPoissonPathLaw
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (Y : ℝ≥0 → Ω → ℕ)
    (P : ℕ → Measure Ω) (law : PopulationLaws)
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hRate : 0 < rate)
    (offspring : PMF ℕ) (hNoNullJumps : offspring 1 = 0)
    (hFiniteOffspringMean : Summable
      (fun k : ℕ => (offspring k).toReal * (k : ℝ)))
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
