-- Prove2me | Theorems.Thm_Kyprianou_Ch01_finiteMeanCompoundPoissonLinearGrowth
-- name    : Kyprianou.Ch01.finiteMeanCompoundPoissonLinearGrowth
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T12:35:59.709261+00:00
-- url     : https://prove2.me/theorems/6c948fb3-5ecb-4da8-953d-12b5d32aa473
-- title:
--   Chapter 1: finite-mean compound Poisson integer paths grow at most linearly almost surely
-- statement:
--   Under the actual finite offspring first-moment assumption, compound Poisson driver, skip-free jump support and jump-mass correspondence, the integer compound Poisson process started at each integer population has an almost-sure finite random linear upper envelope for all nonnegative times. This follows from the Poisson strong law and integrable i.i.d. marks. The universal-in-time bound is essential to control inverse-speed time change.
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

theorem Kyprianou.Ch01.finiteMeanCompoundPoissonLinearGrowth
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
      ∃ C : ℝ, 0 < C ∧
        ∀ t : ℝ≥0,
          (integerCompoundPoisson y arrival marks t ω : ℝ) ≤
            C * (1 + (t : ℝ)) := by
  sorry
