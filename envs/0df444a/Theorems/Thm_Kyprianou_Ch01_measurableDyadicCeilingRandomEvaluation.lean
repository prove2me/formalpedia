-- Prove2me | Theorems.Thm_Kyprianou_Ch01_measurableDyadicCeilingRandomEvaluation
-- name    : Kyprianou.Ch01.measurableDyadicCeilingRandomEvaluation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T18:49:32.457802+00:00
-- url     : https://prove2.me/theorems/eda662fe-e165-43c5-b92b-4f5688598568
-- title:
--   Measurability of a random-time dyadic-ceiling section of a fixed-time measurable process
-- statement:
--   For any real-valued NNReal-indexed process with globally measurable fixed-time sections and any measurable NNReal random time T, the evaluation at the n-th dyadic ceiling approximation to T is globally measurable. Its sampling grid is countable: obtain measurability of the whole path Ω→(NNReal→Real) via measurable_pi_iff, then form the measurable grid evaluator on path×Nat by measurable_from_prod_countable_left and coordinate evaluation. Compose with the measurable pair (full path, Nat.ceil(T*2^n)). This result is independent of sample-path regularity and is the finite-grid piece of an almost-everywhere random-time evaluation theorem.
-- source:
--   Kyprianou (2006) Ch01 §1.3.4 forward Lamperti. Isolates the 200000-heartbeat compiler blocker in generic public Kyprianou.Ch01.aemeasurableRightContinuousRealRandomTimeEvaluation UUID 74ed6524-e545-40dc-bdb3-0bd5fb653135, using the actual accepted dyadic-grid evaluation proof strategy in AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation UUID 8aafec11-d8a5-443c-9386-270a0d5c8a04.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.measurableDyadicCeilingRandomEvaluation
    {Ω : Type*} [MeasurableSpace Ω]
    (F : ℝ≥0 → Ω → ℝ)
    (hMeas : ∀ t : ℝ≥0, Measurable (F t))
    (T : Ω → ℝ≥0) (hT : Measurable T) (n : ℕ) :
    Measurable (fun ω : Ω =>
      F ((⌈T ω * (2 : ℝ≥0) ^ n⌉₊ : ℝ≥0) /
        (2 : ℝ≥0) ^ n) ω) := by
  sorry
