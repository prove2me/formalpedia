-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiNoFirstArrivalWindowAE
-- name    : Kyprianou.Ch01.reverseLampertiNoFirstArrivalWindowAE
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T14:02:44.90861+00:00
-- url     : https://prove2.me/theorems/e493ee2c-47d8-4b91-bbee-396672b0ff01
-- title:
--   Original first-arrival delay forces unchanged inverse-Lamperti population
-- statement:
--   For any initial population y and physical time t, with probability one, if the original first arrival occurs after y*t then the reverse Lamperti population has not yet jumped and is y. For y=0, use infinite inverse-speed density on the initial zero population interval to show absorption. For y>0 use the constant positive y pre-first compound-Poisson path and the reciprocal occupation inverse. The almost-sure form handles exceptional non-regular arrival paths.
-- source:
--   Kyprianou (2006) §1.3.4 inverse speed clock before the first compound-Poisson arrival

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiNoFirstArrivalWindowAE
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q) :
    ∀ (y : ℕ) (t : ℝ≥0), ∀ᵐ ω ∂Q,
      (y : ℝ) * (t : ℝ) < ProbabilityTheory.arrival arrival 0 ω →
      (compoundPoissonToBranching
      (integerCompoundPoisson y arrival marks) t ω).toNat = y := by
  sorry
