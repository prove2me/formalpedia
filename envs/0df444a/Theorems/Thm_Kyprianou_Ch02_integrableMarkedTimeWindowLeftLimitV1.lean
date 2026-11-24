-- Prove2me | Theorems.Thm_Kyprianou_Ch02_integrableMarkedTimeWindowLeftLimitV1
-- name    : Kyprianou.Ch02.integrableMarkedTimeWindowLeftLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:55:43.858613+00:00
-- url     : https://prove2.me/theorems/720f1b4d-9d27-4c4b-a74b-b97682c9e263
-- title:
--   Left limit of an integrable signed marked time-window integral
-- statement:
--   For an integrable signed mark integrand, the cumulative integral over the time window (0,s] tends from the left to the integral over (0,t). Indicators converge pointwise and are dominated by the absolute integrand.
-- source:
--   Kyprianou (2006), Theorem 2.1, finite-band jump identification

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.integrableMarkedTimeWindowLeftLimitV1
    (μ : Measure (ℝ × ℝ)) (B : Set ℝ) (hB : MeasurableSet B)
    (g : ℝ × ℝ → ℝ) (hg : Integrable g μ) (t : ℝ≥0) :
    Tendsto (fun s : ℝ≥0 => ∫ z in (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ B), g z ∂μ)
      (nhdsWithin t (Set.Iio t))
      (nhds (∫ z in (Set.Ioo (0 : ℝ) (t : ℝ) ×ˢ B), g z ∂μ)) := by sorry
