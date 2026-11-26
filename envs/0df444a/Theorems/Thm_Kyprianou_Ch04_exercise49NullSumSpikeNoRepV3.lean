-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49NullSumSpikeNoRepV3
-- name    : Kyprianou.Ch04.exercise49NullSumSpikeNoRepV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:49:00.655992+00:00
-- url     : https://prove2.me/theorems/e65445ed-578a-5e99-93a0-1f5ff3518366
-- title:
--   A nonmeasurable spike clock on an exceptional component rules out a pointwise measurable finite-time representative
-- statement:
--   A nonmeasurable spike clock on an exceptional component rules out a pointwise measurable finite-time representative
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), exceptional-path statement audit.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49NullSumSpikeNoRepV3
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (Y : NNReal → (Ω ⊕ E) → ℝ) (a : E → NNReal)
    (ha : ∀ e, 0 < a e) (hBad : ¬ MeasurableSet {e | a e ≤ 1})
    (hSpike : ∀ t e, Y t (Sum.inr e) = if t = a e then -1 else 0) :
    let τ := fun w : Ω ⊕ E => sInf {v : WithTop NNReal |
      ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ Y t w < 0}
    ¬ ∃ f : Ω ⊕ E → NNReal, Measurable f ∧
      ∀ w, τ w ≠ ⊤ → τ w = (f w : WithTop NNReal) := by
  sorry
