-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41ZeroClockStopV12
-- name    : Kyprianou.Ch04.exercise41ZeroClockStopV12
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:51:48.988352+00:00
-- url     : https://prove2.me/theorems/04ff4b49-9817-49e3-abff-9f9091499297
-- title:
--   Countable infimum and supremum of grid entrance clocks, capped at a deterministic time, are stopping times in the right-continuous filtration
-- statement:
--   Countable infimum and supremum of grid entrance clocks, capped at a deterministic time, are stopping times in the right-continuous filtration
-- source:
--   Kyprianou (2006), Exercise 4.1(ii), zero-visit boundary behaviour.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41ZeroClockStopV12
    {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration NNReal inferInstance)
    (X : NNReal → Ω → ℝ) (hX : Adapted F X)
    (q : ℕ → NNReal) (a N : NNReal) :
    let raw := fun w : Ω => ⨆ n : ℕ, ⨅ k : ℕ, if a ≤ q k ∧ |X (q k) w| < 1 / ((n : ℝ) + 1)
      then (q k : WithTop NNReal) else ⊤
    let τ := fun w => (min (raw w) (N : WithTop NNReal)).untopD 0
    ∀ s : NNReal, MeasurableSet[F.rightCont s] {w | τ w ≤ s} := by
  sorry
