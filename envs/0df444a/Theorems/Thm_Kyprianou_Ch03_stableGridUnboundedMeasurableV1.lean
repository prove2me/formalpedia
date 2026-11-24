-- Prove2me | Theorems.Thm_Kyprianou_Ch03_stableGridUnboundedMeasurableV1
-- name    : Kyprianou.Ch03.stableGridUnboundedMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T18:58:39.241256+00:00
-- url     : https://prove2.me/theorems/46427344-51a4-4302-b634-4c4f738c22e1
-- title:
--   Measurable grid sums with null fixed thresholds are almost surely unbounded
-- statement:
--   Use countably many integer thresholds and the Archimedean property.
-- source:
--   Kyprianou (2006), Exercise 3.7; countable threshold auxiliary.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.stableGridUnboundedMeasurableV1
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℕ → Ω → ℝ) (hnull : ∀ m : ℕ, P (⋂ n : ℕ, {w | Y n w ≤ (m : ℝ)}) = 0) :
    ∀ᵐ w ∂P, ∀ M : ℝ, ∃ n : ℕ, M < Y n w := by sorry
