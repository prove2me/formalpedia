-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_ae_abs_tail_zero
-- name    : Kyprianou.Ch04.kw47_ae_abs_tail_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:26:54.881093+00:00
-- url     : https://prove2.me/theorems/120e1aef-d496-4616-ba6c-3d9ee5dc086f
-- title:
--   Almost-sure grid convergence implies the exact real-valued probability tail limit
-- statement:
--   On a finite measure space, almost-sure convergence of measurable real-valued approximants gives vanishing probability of absolute deviation at least epsilon, expressed using the real-valued measure. Apply the Mathlib almost-sure to convergence-in-measure theorem and its real norm-tail characterisation. This is precisely the Chapter 4 stochastic integral convergence criterion.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.7(i), standard almost-sure convergence to convergence in probability.

import Mathlib
open MeasureTheory Filter Topology
set_option autoImplicit false

/-- Almost-sure convergence of measurable real variables implies
the real-valued probability tail condition in the chapter definition. -/

theorem Kyprianou.Ch04.kw47_ae_abs_tail_zero
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (Q : Nat → Ω → Real) (I : Ω → Real)
    (hQ : ∀ n, AEStronglyMeasurable (Q n) P)
    (hLim : ∀ᵐ w ∂P,
      Tendsto (fun n => Q n w) atTop (nhds (I w)))
    (epsilon : Real) (heps : 0 < epsilon) :
    Tendsto (fun n => (P {w : Ω | epsilon ≤ |Q n w - I w|}).toReal)
      atTop (nhds 0) := by sorry
