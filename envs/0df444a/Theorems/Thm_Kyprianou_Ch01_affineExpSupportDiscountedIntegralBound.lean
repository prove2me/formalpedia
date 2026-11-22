-- Prove2me | Theorems.Thm_Kyprianou_Ch01_affineExpSupportDiscountedIntegralBound
-- name    : Kyprianou.Ch01.affineExpSupportDiscountedIntegralBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T20:41:47.722213+00:00
-- url     : https://prove2.me/theorems/58d032c5-4a8d-48ef-a58b-393746d89895
-- title:
--   Positive-intercept affine-exponential support and unit exponential moment imply a discounted integral bound
-- statement:
--   Abstract measure-theoretic engine for McKean verification. On a probability space, if a measurable bounded value function V has a touching upper support V(z)≤A+B exp(−phi(z−v)) with A≥0 and exact equality at y, and if the discounted exponential of increment Z has expectation one and is integrable, then exp(−qt) E[V(y+Z)]≤V(y) for q,t≥0. Integrate the support, use exp(−phi(y+Z−v))=exp(−phi(y−v))*exp(qt)*exp(−phi Z−qt), and the martingale moment to evaluate the support integral. The nonnegative intercept decreases after discount. This proves semigroup q-excessivity via elementary algebra, without any Ito or Gaussian analytic assumptions. It is a necessary generic helper imported into the original McKean Brownian semigroup theorem, linking it to the main mission graph.
-- source:
--   Abstract affine-exponential supermartingale verification used for Kyprianou (2006) Chapter 1 McKean perpetual put.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.affineExpSupportDiscountedIntegralBound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (V : ℝ → ℝ)
    (K q phi y v A B : ℝ) (t : ℝ≥0)
    (hK : 0 ≤ K) (hq : 0 ≤ q) (hA : 0 ≤ A)
    (hZm : Measurable Z) (hVm : Measurable V)
    (hVbound : ∀ z, ‖V z‖ ≤ K)
    (hMaj : ∀ z, V z ≤ A + B * Real.exp (-phi * (z - v)))
    (hTouch : V y = A + B * Real.exp (-phi * (y - v)))
    (hMoment :
      Integrable (fun ω => Real.exp (-phi * Z ω - q * (t : ℝ))) P ∧
      (∫ ω, Real.exp (-phi * Z ω - q * (t : ℝ)) ∂P) = 1) :
    Real.exp (-q * (t : ℝ)) * (∫ ω, V (y + Z ω) ∂P) ≤ V y := by sorry
