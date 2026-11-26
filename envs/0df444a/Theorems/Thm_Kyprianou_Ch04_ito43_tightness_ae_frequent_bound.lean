-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_tightness_ae_frequent_bound
-- name    : Kyprianou.Ch04.ito43_tightness_ae_frequent_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:19:28.62812+00:00
-- url     : https://prove2.me/theorems/5463c8e6-77ff-587d-8901-0e7cc42b1bc9
-- title:
--   Uniform outer probability tightness gives an almost sure frequent finite bound
-- statement:
--   Uniform outer probability tightness gives an almost sure frequent finite bound.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal Topology
set_option autoImplicit false

/-- Eventual uniform upper-tail bounds imply an almost surely finite frequent bound.
The events need not be measurable: continuity from below holds for outer measures. -/

theorem Kyprianou.Ch04.ito43_tightness_ae_frequent_bound {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Q : ℕ → Ω → ℝ)
    (hQ : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n in atTop, (P {w | C ≤ Q n w}).toReal ≤ η) :
    ∀ᵐ w ∂P, ∃ C : ℝ, ∃ᶠ n in atTop, Q n w < C := by sorry
