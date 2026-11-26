-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_real_measurable_tail
-- name    : Kyprianou.Ch04.ito43_real_measurable_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:34:47.920805+00:00
-- url     : https://prove2.me/theorems/77778490-6722-50a2-8aab-c5362a67c869
-- title:
--   Real measurable random variables have arbitrarily small upper tails
-- statement:
--   A finite measurable real random variable is bounded by a deterministic positive constant outside an event of arbitrarily small probability.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal Topology
set_option autoImplicit false

/-- A finite real measurable random variable admits a deterministic upper bound
outside a set of arbitrarily small probability. -/

theorem Kyprianou.Ch04.ito43_real_measurable_tail {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (M : Ω → ℝ) (hM : Measurable M)
    (e : ℝ) (he : 0 < e) : ∃ R : ℝ, 0 < R ∧ (P {w | R < M w}).toReal < e := by sorry
