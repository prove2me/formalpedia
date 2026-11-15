-- Prove2me | Theorems.Thm_Kyprianou_Ch01_queueWorkload_initial_difference_le
-- name    : Kyprianou.Ch01.queueWorkload_initial_difference_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:30:23.7076+00:00
-- url     : https://prove2.me/theorems/30386be9-5d16-48fb-be6c-9e67e76c61cd
-- title:
--   Queue workload increase is bounded by the initial backlog increment
-- statement:
--   The M/G/1 reflected workload at any time increases by no more than an increase in initial backlog.
-- source:
--   Kyprianou (2006), Chapter 1, queueing and risk process discussion §§1.3.2–1.3.3, based on canonical source definition queueWorkload and original v13 source proof.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.queueWorkload_initial_difference_le
    {Ω : Type*} [MeasurableSpace Ω]
    (arrival claims : ℕ → Ω → ℝ) (t : ℝ≥0) (ω : Ω)
    (w1 w2 : ℝ) (h : w1 ≤ w2) :
    queueWorkload arrival claims w2 t ω -
      queueWorkload arrival claims w1 t ω ≤ w2 - w1 := by sorry
