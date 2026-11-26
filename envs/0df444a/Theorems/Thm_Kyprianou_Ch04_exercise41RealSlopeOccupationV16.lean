-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41RealSlopeOccupationV16
-- name    : Kyprianou.Ch04.exercise41RealSlopeOccupationV16
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T13:11:19.304796+00:00
-- url     : https://prove2.me/theorems/87af1f7d-d79c-5326-bf16-738825121166
-- title:
--   Almost-everywhere strictly increasing right germ gives zero time occupation of every fixed level
-- statement:
--   Almost-everywhere strictly increasing right germ gives zero time occupation of every fixed level
-- source:
--   Kyprianou (2006), Exercise 4.1(ii), exclusion of continuous touches from above.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41RealSlopeOccupationV16
    (x : ℝ → ℝ)
    (h : ∀ᵐ s ∂(volume : Measure ℝ), 0 ≤ s → ∃ e : ℝ, 0 < e ∧
      ∀ v ∈ Ioo s (s + e), x s < x v) :
    ∀ b : ℝ, volume {s : ℝ | 0 ≤ s ∧ x s = b} = 0 := by
  sorry
