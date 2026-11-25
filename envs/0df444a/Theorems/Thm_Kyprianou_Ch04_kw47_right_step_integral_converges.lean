-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_right_step_integral_converges
-- name    : Kyprianou.Ch04.kw47_right_step_integral_converges
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T11:40:19.896584+00:00
-- url     : https://prove2.me/theorems/32f9f505-abc3-43bc-a78b-dfa6dbd7ecc1
-- title:
--   Bounded right-endpoint evaluation under a finite measure
-- statement:
--   For right-continuous f, composition with right-approaching mesh endpoint functions converges pointwise, and the finite measure and uniform bound give dominated convergence.
-- source:
--   Kyprianou (2006), Exercise 4.7; deterministic product-grid martingale transfer.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch04.kw47_right_step_integral_converges
    (mu : Measure Real) [IsFiniteMeasure mu]
    (f : Real → Real) (B : Real) (r : Nat → Real → Real)
    (hf : Measurable f) (hr : ∀ n, Measurable (r n))
    (hbound : ∀ x, ‖f x‖ ≤ B)
    (hlim : ∀ᵐ x ∂mu, Tendsto (fun n => r n x) atTop (nhdsWithin x (Ici x)))
    (hRight : ∀ x, ContinuousWithinAt f (Ici x) x) :
    Tendsto (fun n => ∫ x, f (r n x) ∂mu) atTop (nhds (∫ x, f x ∂mu)) := by sorry
