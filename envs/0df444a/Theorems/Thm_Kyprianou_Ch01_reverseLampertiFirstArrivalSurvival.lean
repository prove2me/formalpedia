-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiFirstArrivalSurvival
-- name    : Kyprianou.Ch01.reverseLampertiFirstArrivalSurvival
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T10:54:00.561808+00:00
-- url     : https://prove2.me/theorems/01ffae6d-b4d3-4117-86eb-3a97eec15a12
-- title:
--   Exponential survival of the compound Poisson first arrival at the initial population clock
-- statement:
--   For a source-faithful compound Poisson driver of rate r>0, initial population y and branching-time horizon t≥0, the probability that the first raw Poisson arrival is strictly later than the corresponding initial linear clock y*t is exactly exp(-r*y*t). This holds for arbitrary mark law and no finite offspring moment. Reuse the already Proved ProbabilityTheory.arrival_survival at index zero.
-- source:
--   Kyprianou (2006) Chapter 1 section 1.3.4 reverse Lamperti first-jump clock; already Proved ProbabilityTheory.arrival_survival UUID 9aac65ab-95fc-4684-9332-131ff6826e92.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiFirstArrivalSurvival
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (y : ℕ) (t : ℝ≥0) :
    (Q {ω | (y : ℝ) * (t : ℝ) <
      ProbabilityTheory.arrival arrival 0 ω}).toReal =
      Real.exp (-((rate : ℝ) * ((y : ℝ) * (t : ℝ)))) := by
  sorry
