-- Prove2me | Theorems.Thm_Kyprianou_Ch01_compoundPoissonMarkedFirstTwoClockProductFactor
-- name    : Kyprianou.Ch01.compoundPoissonMarkedFirstTwoClockProductFactor
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T12:41:09.593125+00:00
-- url     : https://prove2.me/theorems/3b427102-d808-428b-bba2-e79697195453
-- title:
--   Marked first two arrivals probability bounded by first-arrival probability times offspring-averaged second-arrival factor
-- statement:
--   For the source compound Poisson driver, use joint independence of first interarrival τ0, second interarrival τ1 and first mark marks0 to bound the marked two-jump event by P(τ0≤y*t) times the sum over all offspring k of p(k)*(1-exp(-rate*(y+k)*t)). This expresses independence and mark disintegration without assuming a finite offspring mean; it is the true remaining probabilistic part of the marked two-event clock bound.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.compoundPoissonMarkedFirstTwoClockProductFactor
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k)
    (y : ℕ) (t : ℝ≥0) :
    (Q {ω | ∃ k : ℕ,
          marks 0 ω = (k : ℝ) - 1 ∧
          ProbabilityTheory.arrival arrival 0 ω ≤ (y : ℝ) * (t : ℝ) ∧
          ProbabilityTheory.arrival arrival 1 ω ≤
            ProbabilityTheory.arrival arrival 0 ω +
              (((y + k : ℕ) : ℝ)) * (t : ℝ)}).toReal ≤
      (Q {ω | ProbabilityTheory.arrival arrival 0 ω ≤
        (y : ℝ) * (t : ℝ)}).toReal *
        (∑' k : ℕ, (offspring k).toReal *
          (1 - Real.exp (-((rate : ℝ) * (((y + k : ℕ) : ℝ)) * (t : ℝ))))) := by
  sorry
