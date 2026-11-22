-- Prove2me | Theorems.Thm_Kyprianou_Ch01_boundedConvergenceExpectedUpper
-- name    : Kyprianou.Ch01.boundedConvergenceExpectedUpper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T18:52:45.759654+00:00
-- url     : https://prove2.me/theorems/536cabb6-c89f-4c2d-91e6-f5915821e047
-- title:
--   Uniform bounded convergence transports a finite-horizon expectation upper bound to the limit
-- statement:
--   For a probability measure, a measurable uniformly bounded family f(n) converging pointwise to a measurable uniformly bounded g, any common upper bound C on the integrals of f(n) also bounds the integral of g, and g is integrable. Invoke the existing Proved FamousTheorems.bounded_convergence for the limit of integrals, Integrable.of_bound for integrability of g, and the closedness of the order interval (-infinity,C] under limits. This bridges the proved finite-horizon optional-stopping estimates to the exact infinite-time McKean payoff without losing integrability.
-- source:
--   Kyprianou 2006 Chapter 1 Theorem 1.13; bounded convergence in optional stopping.

import Mathlib
import Theorems.Thm_FamousTheorems_bounded_convergence
open MeasureTheory Filter
set_option autoImplicit false

theorem Kyprianou.Ch01.boundedConvergenceExpectedUpper
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ) (K C : ℝ)
    (hf : ∀ n, Measurable (f n))
    (hg : Measurable g)
    (hfBound : ∀ n ω, ‖f n ω‖ ≤ K)
    (hgBound : ∀ ω, ‖g ω‖ ≤ K)
    (hlim : ∀ ω, Filter.Tendsto (fun n => f n ω)
      Filter.atTop (nhds (g ω)))
    (hUpper : ∀ n, (∫ ω, f n ω ∂P) ≤ C) :
    Integrable g P ∧ (∫ ω, g ω ∂P) ≤ C := by sorry
