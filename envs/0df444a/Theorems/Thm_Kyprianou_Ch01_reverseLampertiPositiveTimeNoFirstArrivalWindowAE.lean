-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiPositiveTimeNoFirstArrivalWindowAE
-- name    : Kyprianou.Ch01.reverseLampertiPositiveTimeNoFirstArrivalWindowAE
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T14:25:41.52112+00:00
-- url     : https://prove2.me/theorems/9fc0562c-1039-4da0-a513-ac750b962f44
-- title:
--   No source jump before positive inverse Lamperti time implies unchanged population
-- statement:
--   For strictly positive physical time t, if no compound-Poisson source jump has occurred before source horizon y*t, the inverse-speed occupation clock maps t into the pre-first-jump source interval, or remains at zero when y=0. Hence the time-changed branching population remains y almost surely. Separate the positive-time clock argument from the previously Proved zero-time boundary.
-- source:
--   Kyprianou (2006) §1.3.4, positive-time no-arrival inverse-speed occupation

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiPositiveTimeNoFirstArrivalWindowAE
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q) :
    ∀ (y : ℕ) (t : ℝ≥0), 0 < t → ∀ᵐ ω ∂Q,
      (y : ℝ) * (t : ℝ) < ProbabilityTheory.arrival arrival 0 ω →
      (compoundPoissonToBranching
      (integerCompoundPoisson y arrival marks) t ω).toNat = y := by
  sorry
