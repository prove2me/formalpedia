-- Prove2me | Theorems.Thm_Kyprianou_Ch04_boundedContinuousEventuallyEqualExpectations
-- name    : Kyprianou.Ch04.boundedContinuousEventuallyEqualExpectations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:32:47.588973+00:00
-- url     : https://prove2.me/theorems/18ea766d-c961-4a69-9225-220dcf86ae15
-- title:
--   Almost sure eventual equality preserves the limit of bounded continuous expectations.
-- statement:
--   Almost sure eventual equality preserves the limit of bounded continuous expectations.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.10

import Mathlib
open MeasureTheory Filter
open scoped NNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.boundedContinuousEventuallyEqualExpectations {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D W : NNReal → Ω → ℝ)
    (hD : ∀ t, Measurable (D t)) (hW : ∀ t, Measurable (W t))
    (he : ∀ᵐ z ∂P, ∀ᶠ t in atTop, W t z = D t z)
    (f : BoundedContinuousFunction ℝ ℝ) (a : ℝ)
    (hlim : Tendsto (fun t => ∫ z, f (D t z) ∂P) atTop (nhds a)) :
    Tendsto (fun t => ∫ z, f (W t z) ∂P) atTop (nhds a) := by
  sorry
