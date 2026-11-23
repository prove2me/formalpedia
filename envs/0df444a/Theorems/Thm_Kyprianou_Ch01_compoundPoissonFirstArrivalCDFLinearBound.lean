-- Prove2me | Theorems.Thm_Kyprianou_Ch01_compoundPoissonFirstArrivalCDFLinearBound
-- name    : Kyprianou.Ch01.compoundPoissonFirstArrivalCDFLinearBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T12:41:00.919417+00:00
-- url     : https://prove2.me/theorems/c7d1a127-ff68-4a31-a024-8389aaa64e96
-- title:
--   Compound-Poisson first-arrival CDF bounded by rate times raw horizon
-- statement:
--   For a jointly independent exponential/mark compound Poisson driver, the probability of the first raw arrival by u≥0 is at most rate*u. Use the law_interarrival 0 exponential CDF and Real.add_one_le_exp. This is the first-event factor of a marked second-arrival probability estimate.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.compoundPoissonFirstArrivalCDFLinearBound
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (u : ℝ) (hu : 0 ≤ u) :
    (Q {ω | ProbabilityTheory.arrival arrival 0 ω ≤ u}).toReal ≤
      (rate : ℝ) * u := by
  sorry
