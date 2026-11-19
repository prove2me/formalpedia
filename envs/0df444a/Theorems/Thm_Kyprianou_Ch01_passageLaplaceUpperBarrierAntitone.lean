-- Prove2me | Theorems.Thm_Kyprianou_Ch01_passageLaplaceUpperBarrierAntitone
-- name    : Kyprianou.Ch01.passageLaplaceUpperBarrierAntitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:11:58.762618+00:00
-- url     : https://prove2.me/theorems/00c39db4-3f48-42a4-b646-4ad332210d48
-- title:
--   Discounted strict upper-passage payoff decreases with higher barriers
-- statement:
--   For any sample path and nonnegative discount rate, the strict upper-passage discounted payoff (zero if the barrier is never exceeded) is decreasing in the barrier, using the exact original firstUpperPassage and passageLaplace definitions and retaining the infinite-time cases. This provides the deterministic comparison needed for Brownian zero-barrier recovery.
-- source:
--   Kyprianou 2006 Chapter 1, Exercise 1.10: Brownian first-passage transform and zero-level boundary.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Set Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.passageLaplaceUpperBarrierAntitone
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (a b : ℝ) (hab : a ≤ b)
    (q : ℝ) (hq : 0 ≤ q) (ω : Ω) :
    passageLaplace (firstUpperPassage X b) q ω ≤
      passageLaplace (firstUpperPassage X a) q ω := by
  sorry
