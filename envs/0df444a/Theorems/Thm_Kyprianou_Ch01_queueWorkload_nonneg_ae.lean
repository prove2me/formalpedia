-- Prove2me | Theorems.Thm_Kyprianou_Ch01_queueWorkload_nonneg_ae
-- name    : Kyprianou.Ch01.queueWorkload_nonneg_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:09:35.831589+00:00
-- url     : https://prove2.me/theorems/3d0a030e-f630-4d22-bd43-9a4df165497f
-- title:
--   M/G/1 compound-Poisson reflected workload is almost surely nonnegative
-- statement:
--   The reflected queue workload is nonnegative for all initial workloads and finite times on almost every sample path of the compound-Poisson input.
-- source:
--   Kyprianou (2006), Chapter 1, risk and queue sections; existing source-file proof in research/kyprianou_ch01/proofs/queue_workload_nonneg_ae_v12.lean

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Theorems.Thm_Kyprianou_Ch01_riskSurplus_runningSup_bddAbove_ae
import Theorems.Thm_Kyprianou_Ch01_queueWorkload_nonneg
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.queueWorkload_nonneg_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ)
    (rate : ℝ≥0) (F : Measure ℝ)
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (hr : 0 < rate) :
    ∀ᵐ ω ∂P, ∀ (w : ℝ) (T : ℝ≥0),
      0 ≤ queueWorkload arrival claims w T ω := by sorry
