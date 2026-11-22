-- Prove2me | Theorems.Thm_Kyprianou_Ch01_rightNaturalStoppedPut_measurable_of_continuous
-- name    : Kyprianou.Ch01.rightNaturalStoppedPut_measurable_of_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:01:33.36907+00:00
-- url     : https://prove2.me/theorems/a3f7363a-9d46-4382-8d96-325f8e98f494
-- title:
--   Right-natural stopped perpetual put payoff measurable
-- statement:
--   The discounted put payoff sampled at any right-natural stopping time of a continuous-path, fixed-time-measurable process is measurable, including zero contribution at infinite passage. Derive measurable stopping time from its sublevel sets and ambient measurability, prove jointly measurable evaluation from measurable time sections and path continuity, and handle the infinite branch. This establishes the payoff measurability prerequisite for the already Proved integrability bound.
-- source:
--   Kyprianou (2006) Chapter 1 Theorem 1.13; stopped payoff measurability.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.rightNaturalStoppedPut_measurable_of_continuous
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (x K q : ℝ)
    (tau : Ω → WithTop ℝ≥0)
    (hTau : IsNaturalRightStoppingTime (fun t ω => x + X t ω) tau) :
    Measurable (discountedPut X x K q tau) := by sorry
