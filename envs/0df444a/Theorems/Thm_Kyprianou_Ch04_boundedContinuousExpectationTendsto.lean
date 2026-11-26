-- Prove2me | Theorems.Thm_Kyprianou_Ch04_boundedContinuousExpectationTendsto
-- name    : Kyprianou.Ch04.boundedContinuousExpectationTendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:21:13.967282+00:00
-- url     : https://prove2.me/theorems/d1b154d4-84c3-5d99-bec9-69fa22c793f7
-- title:
--   Bounded continuous expectations converge under almost-sure limits
-- statement:
--   Apply filter dominated convergence to the bounded continuous test function composed with the measurable random variables.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.10

import Mathlib
open MeasureTheory Filter
open scoped NNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.boundedContinuousExpectationTendsto
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (Z : Ω → ℝ)
    (hm : ∀ t, Measurable (X t))
    (hlim : ∀ᵐ z ∂P, Tendsto (fun t => X t z) atTop (nhds (Z z)))
    (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun t => ∫ z, f (X t z) ∂P) atTop (nhds (∫ z, f (Z z) ∂P)) := by
  sorry
