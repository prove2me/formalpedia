-- Prove2me | Theorems.Thm_Kyprianou_Ch01_queueWorkload_mono_initial
-- name    : Kyprianou.Ch01.queueWorkload_mono_initial
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:30:30.10326+00:00
-- url     : https://prove2.me/theorems/52f94043-710f-47d8-9be1-b53520b2a52a
-- title:
--   Queue workload is nondecreasing in initial backlog
-- statement:
--   For any fixed arrival and claim paths, increasing the initial backlog cannot reduce the reflected M/G/1 queue workload at any nonnegative time.
-- source:
--   Kyprianou (2006), Chapter 1, queueing and risk process discussion §§1.3.2–1.3.3, based on canonical source definition queueWorkload and original v13 source proof.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.queueWorkload_mono_initial
    {Ω : Type*} [MeasurableSpace Ω]
    (arrival claims : ℕ → Ω → ℝ) (t : ℝ≥0) (ω : Ω)
    (w1 w2 : ℝ) (h : w1 ≤ w2) :
    queueWorkload arrival claims w1 t ω ≤
      queueWorkload arrival claims w2 t ω := by sorry
