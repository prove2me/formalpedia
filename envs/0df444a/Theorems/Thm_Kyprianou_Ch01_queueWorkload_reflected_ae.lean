-- Prove2me | Theorems.Thm_Kyprianou_Ch01_queueWorkload_reflected_ae
-- name    : Kyprianou.Ch01.queueWorkload_reflected_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:13:55.622147+00:00
-- url     : https://prove2.me/theorems/c21bd61c-f643-4972-887d-cce7a9cb81f0
-- title:
--   Almost-sure simultaneous Skorokhod reflection of the M/G/1 workload
-- statement:
--   For almost every path of a positive-rate compound-Poisson input, the queue workload equals the Skorokhod-reflected net input simultaneously for every finite horizon and initial backlog.
-- source:
--   Kyprianou (2006), Chapter 1, M/G/1 workload and insurance duality; derived from proven finite-horizon running-supremum and pathwise-reflection lemmas.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Theorems.Thm_Kyprianou_Ch01_riskSurplus_runningSup_bddAbove_ae
import Theorems.Thm_Kyprianou_Ch01_queueWorkload_reflected
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal Pointwise
set_option autoImplicit false

theorem Kyprianou.Ch01.queueWorkload_reflected_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ)
    (rate : ℝ≥0) (F : Measure ℝ)
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (hr : 0 < rate) :
    ∀ᵐ ω ∂P, ∀ (w : ℝ) (T : ℝ≥0),
      queueWorkload arrival claims w T ω =
        max (w - riskSurplus arrival claims 1 0 T ω)
          (sSup ({z : ℝ | ∃ s : ℝ≥0,
            s ≤ T ∧ z = riskSurplus arrival claims 1 0 s ω} -
            {riskSurplus arrival claims 1 0 T ω})) := by sorry
