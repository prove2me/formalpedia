-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_measurable_centered_prefix_maximal
-- name    : Kyprianou.Ch04.ito43_measurable_centered_prefix_maximal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:00:20.019384+00:00
-- url     : https://prove2.me/theorems/77ab8dc4-bc76-5eea-9b32-7c7d80c7679f
-- title:
--   Measurable independent centred prefix bound from individual variances
-- statement:
--   Apply Durrett's proved Kolmogorov maximal inequality. The variance of a finite sum of independent square integrable coordinates is the sum of their variances, each at most the given bound. The zero-length prefix cannot cross the positive threshold.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_measurable_centered_prefix_maximal {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hm : ∀ k, Measurable (Y k)) (hi : iIndepFun Y P)
    (hL : ∀ k, MemLp (Y k) 2 P) (hmean : ∀ k, (∫ w, Y k w ∂P) = 0)
    (V : ℝ) (hv : ∀ k, variance (Y k) P ≤ V)
    (n : ℕ) (e : ℝ) (he : 0 < e) :
    (P {w | ∃ j ≤ n, e ≤ |∑ k ∈ Finset.range j, Y k w|}).toReal
      ≤ (n:ℝ)*V/e^2 := by sorry
