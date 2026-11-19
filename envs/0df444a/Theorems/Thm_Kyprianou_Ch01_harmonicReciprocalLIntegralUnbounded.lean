-- Prove2me | Theorems.Thm_Kyprianou_Ch01_harmonicReciprocalLIntegralUnbounded
-- name    : Kyprianou.Ch01.harmonicReciprocalLIntegralUnbounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T12:39:04.02618+00:00
-- url     : https://prove2.me/theorems/48d02c33-afaa-41b4-9dcb-1a0d1417fa20
-- title:
--   Divergence of the positive harmonic reciprocal lower integral on the half-line
-- statement:
--   For every strictly positive constant C, the extended Lebesgue integral of 1/[C(1+r)] over the positive interval from zero to s grows beyond any fixed finite bound as s increases. This is the analytic harmonic-integral comparison required for inverse-speed clock non-explosion. It follows from the logarithmic antiderivative and logarithm tending to infinity.
-- source:
--   Elementary real analysis: divergence of the harmonic integral and Kyprianou (2006), Chapter 1 section 1.3.4 inverse occupation clock.

import Mathlib
open MeasureTheory Real Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.harmonicReciprocalLIntegralUnbounded
    (C : ℝ) (hC : 0 < C) :
    ∀ t : ℝ≥0, ∃ s : ℝ≥0,
      (t : ℝ≥0∞) <
        (∫⁻ r in Set.Ioc (0 : ℝ) (s : ℝ),
          (ENNReal.ofReal (C * (1 + r)))⁻¹ ∂volume) := by
  sorry
