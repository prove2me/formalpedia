-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstUpperPassageBarrierMonotone
-- name    : Kyprianou.Ch01.firstUpperPassageBarrierMonotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:07:05.267498+00:00
-- url     : https://prove2.me/theorems/ff2b290b-f1bb-4e08-b8dd-0856c8f50c5c
-- title:
--   Strict positive-time upper-passage first hitting time is nondecreasing with its barrier
-- statement:
--   For any path with nonnegative time domain and any real barriers a≤b, the original first strictly positive-time upper passage of the lower barrier a is no later (in WithTop ℝ≥0) than the first passage of higher barrier b, including nonattainment and infinite first passage. This is a deterministic consequence of inclusion of strict upcrossing event sets.
-- source:
--   Kyprianou 2006 Ch1 Exercise 1.10, first-passage threshold-monotonicity used to derive the zero-barrier limit from positive barriers.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Set Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstUpperPassageBarrierMonotone
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (a b : ℝ) (hab : a ≤ b) (ω : Ω) :
    firstUpperPassage X a ω ≤ firstUpperPassage X b ω := by
  sorry
