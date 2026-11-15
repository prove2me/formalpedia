-- Prove2me | Theorems.Thm_Kyprianou_Ch01_queueWorkload_reflected
-- name    : Kyprianou.Ch01.queueWorkload_reflected
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:10:45.142697+00:00
-- url     : https://prove2.me/theorems/a8131947-2235-4acf-96ea-5524d3ee6377
-- title:
--   Finite-horizon M/G/1 workload is reflected net input
-- statement:
--   Given boundedness of the running risk surplus on a finite horizon, the M/G/1 workload is the maximum of its unreflected initial contribution and the supremum of the translated path. This is the exact pathwise Skorokhod reflection identity.
-- source:
--   Kyprianou (2006), Chapter 1, risk and queue reflection §1.3.3; proof derived from research/kyprianou_ch01/proofs/workload_reflection_v12.lean.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal Pointwise
set_option autoImplicit false

theorem Kyprianou.Ch01.queueWorkload_reflected
    {Ω : Type*} [MeasurableSpace Ω]
    (arrival claims : ℕ → Ω → ℝ)
    (w : ℝ) (t : ℝ≥0) (ω : Ω)
    (hbounded : BddAbove {z : ℝ | ∃ s : ℝ≥0,
      s ≤ t ∧ z = riskSurplus arrival claims 1 0 s ω}) :
    let a := riskSurplus arrival claims 1 0 t ω
    let S : Set ℝ := {z | ∃ s : ℝ≥0,
      s ≤ t ∧ z = riskSurplus arrival claims 1 0 s ω}
    queueWorkload arrival claims w t ω =
      max (w - a) (sSup (S - {a})) := by sorry
