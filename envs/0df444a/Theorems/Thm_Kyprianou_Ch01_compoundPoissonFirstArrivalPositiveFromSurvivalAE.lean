-- Prove2me | Theorems.Thm_Kyprianou_Ch01_compoundPoissonFirstArrivalPositiveFromSurvivalAE
-- name    : Kyprianou.Ch01.compoundPoissonFirstArrivalPositiveFromSurvivalAE
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T14:11:55.314914+00:00
-- url     : https://prove2.me/theorems/3932a98b-ba1b-48fc-b326-1af809314ee6
-- title:
--   Positive first compound-Poisson arrival from its public survival law
-- statement:
--   The first exponential interarrival is strictly positive almost surely. From the previously Proved public first-arrival survival identity, at time zero the event of no first arrival has probability one. Convert the real probability to ENNReal probability one and apply the measurable probability-one a.e. equivalence. This reuses the existing public survival theorem without importing a private source proof.
-- source:
--   Kyprianou (2006) §1.3.4, exponential interarrival distribution

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.compoundPoissonFirstArrivalPositiveFromSurvivalAE
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
 :
    ∀ᵐ ω ∂Q, 0 < ProbabilityTheory.arrival arrival 0 ω := by
  sorry
