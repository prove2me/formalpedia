-- Prove2me | Theorems.Thm_Kyprianou_Ch01_compoundPoissonMarkedFirstTwoClockUpperBound
-- name    : Kyprianou.Ch01.compoundPoissonMarkedFirstTwoClockUpperBound
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T12:36:08.966805+00:00
-- url     : https://prove2.me/theorems/c94da83c-826d-42d1-9e76-c5837e27db50
-- title:
--   Independent marked first-two exponential clock probability upper bound
-- statement:
--   Given IsCompoundPoissonDriver with joint independence and first-mark mass offspring k, probability that first raw arrival occurs before y*t and second raw interarrival is at most (y+k)*t when first mark k-1 is bounded by rate*y*t times the offspring-weighted 1-exp(-rate*(y+k)*t). Use independent exponential interarrivals and marks, including tail 1-exp and 1-exp(-u)≤u. No finite offspring mean.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.compoundPoissonMarkedFirstTwoClockUpperBound
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
      ((rate : ℝ) * (y : ℝ)) * (t : ℝ) *
        (∑' k : ℕ, (offspring k).toReal *
          (1 - Real.exp (-((rate : ℝ) * (((y + k : ℕ) : ℝ)) * (t : ℝ))))) := by
  sorry
