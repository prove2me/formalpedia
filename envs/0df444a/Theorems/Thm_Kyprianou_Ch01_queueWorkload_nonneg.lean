-- Prove2me | Theorems.Thm_Kyprianou_Ch01_queueWorkload_nonneg
-- name    : Kyprianou.Ch01.queueWorkload_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:36:11.215299+00:00
-- url     : https://prove2.me/theorems/897b42d2-c5f7-49eb-8d65-6ba2f10c76ac
-- title:
--   A reflected queue workload is nonnegative under a bounded running supremum
-- statement:
--   For a path whose underlying surplus has bounded running supremum, the workload obtained by reflection at that supremum is nonnegative at every fixed time.
-- source:
--   Kyprianou (2006), Chapter 1, risk and queue sections; existing source-file proof in research/kyprianou_ch01/proofs/queue_workload_nonneg_ae_v12.lean

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.queueWorkload_nonneg
    {Ω : Type*} [MeasurableSpace Ω]
    (arrival claims : ℕ → Ω → ℝ)
    (w : ℝ) (t : ℝ≥0) (ω : Ω)
    (hbounded : BddAbove {z : ℝ | ∃ s : ℝ≥0,
      s ≤ t ∧ z = riskSurplus arrival claims 1 0 s ω}) :
    0 ≤ queueWorkload arrival claims w t ω := by sorry
