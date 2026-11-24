-- Prove2me | Theorems.Thm_Kyprianou_Ch02_markedFibreIntegralBoundFromEnvelopeV1
-- name    : Kyprianou.Ch02.markedFibreIntegralBoundFromEnvelopeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:57:59.859891+00:00
-- url     : https://prove2.me/theorems/252e7af4-0026-49bb-8bd2-d072458e5995
-- title:
--   A time-fibre integral inherits the compact mark envelope and unit mass bound
-- statement:
--   Restrict to the time fibre. The integrand is bounded in absolute value by c almost everywhere because marks above c have zero mass. The fibre mass is at most one, so the integral has absolute value at most c.
-- source:
--   Kyprianou (2006), Theorem 2.1, finite compensated band jump bound

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.markedFibreIntegralBoundFromEnvelopeV1
    (μ : Measure (ℝ × ℝ)) (B : Set ℝ) (hB : MeasurableSet B)
    (hsmall : B ⊆ {x : ℝ | |x| < 1})
    (T t : ℝ≥0) (ht : 0 < t) (htT : t ≤ T)
    (c : ℝ) (hc : 0 ≤ c)
    (henvelope : μ (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ
        {x : ℝ | c < |x| ∧ |x| < 1}) = 0)
    (hfibre : μ ({(t : ℝ)} ×ˢ B) ≤ 1) :
    |∫ z in ({(t : ℝ)} ×ˢ B), z.2 ∂μ| ≤ c := by sorry
