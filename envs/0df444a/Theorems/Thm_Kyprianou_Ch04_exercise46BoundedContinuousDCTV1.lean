-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46BoundedContinuousDCTV1
-- name    : Kyprianou.Ch04.exercise46BoundedContinuousDCTV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:26:29.793571+00:00
-- url     : https://prove2.me/theorems/a536bf11-a5cf-548b-b709-7ab3c6da347b
-- title:
--   Bounded continuous payoff dominated convergence
-- statement:
--   Bounded continuous payoff dominated convergence
-- source:
--   Kyprianou (2006), Exercise 4.6.

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46BoundedContinuousDCTV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (M : Nat → Omega → Real) (Mlim : Omega → Real)
    (hM : ∀ n, Measurable (M n))
    (hlim : ∀ᵐ w ∂P, Tendsto (fun n => M n w) atTop (nhds (Mlim w)))
    (f : BoundedContinuousFunction Real Real) :
    Tendsto (fun n => ∫ w, f (M n w) ∂P) atTop
      (nhds (∫ w, f (Mlim w) ∂P)) := by
  sorry
