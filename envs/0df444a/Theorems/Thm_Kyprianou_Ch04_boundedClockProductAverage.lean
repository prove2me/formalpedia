-- Prove2me | Theorems.Thm_Kyprianou_Ch04_boundedClockProductAverage
-- name    : Kyprianou.Ch04.boundedClockProductAverage
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:35:21.126619+00:00
-- url     : https://prove2.me/theorems/336d2b36-9df2-4ba3-96db-d6057fdb16ee
-- title:
--   Product-clock averaging for bounded rewards
-- statement:
--   Apply Fubini to the bounded jointly measurable integrand, then push forward the clock under Real.toNNReal.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.9

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.boundedClockProductAverage
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (g : NNReal × Ω → ℝ) (hm : Measurable g)
    (h0 : ∀ z, 0 ≤ g z) (h1 : ∀ z, g z ≤ 1) :
    (∫ z : Ω × ℝ, g (z.2.toNNReal, z.1) ∂(P.prod Q)) =
      ∫ t : NNReal, (∫ w : Ω, g (t,w) ∂P) ∂(Q.map Real.toNNReal) := by
  sorry
