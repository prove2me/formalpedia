-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_bounded_nonnegative_variance
-- name    : Kyprianou.Ch04.ito43_bounded_nonnegative_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:56:44.774922+00:00
-- url     : https://prove2.me/theorems/579ecbbf-3a88-5620-9676-9e52f0ccdc7d
-- title:
--   Bounded nonnegative random variables have variance bounded by maximum times mean
-- statement:
--   Variance is at most the second moment, and the pointwise squared value is bounded by the maximum times the value.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_bounded_nonnegative_variance {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Ω → ℝ) (C : ℝ) (hC : 0 ≤ C) (hm : AEMeasurable F P)
    (hb : ∀ᵐ w ∂P, 0 ≤ F w ∧ F w ≤ C) :
    MemLp F 2 P ∧ variance F P ≤ C*(∫ w, F w ∂P) := by sorry
