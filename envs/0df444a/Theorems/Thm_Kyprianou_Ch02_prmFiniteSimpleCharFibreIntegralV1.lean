-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteSimpleCharFibreIntegralV1
-- name    : Kyprianou.Ch02.prmFiniteSimpleCharFibreIntegralV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T21:10:10.109994+00:00
-- url     : https://prove2.me/theorems/1039820b-3f03-4fce-8ac8-cc486b3e95b4
-- title:
--   Complex characteristic integrand integral equals finite mark-fibre sum
-- statement:
--   For a real simple mark function f, integrate the finite-range complex function exp(i ξ f(x))−1 over a finite-measure B by partitioning B into the finitely many measurable fibres f=x. Use SimpleFunc.comp/map and SimpleFunc.integral_eq_sum, or integral_finset_sum with indicator fibres, and finite ν(B). No first-moment assumption. Required child of optional Chapter 2 finite simple marked exponent.
-- source:
--   Kyprianou (2006) Chapter 2 Eq. (2.3).

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteSimpleCharFibreIntegralV1
    (ν : Measure ℝ) [SigmaFinite ν]
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (f : SimpleFunc ℝ ℝ) (ξ : ℝ) :
    (∫ x in B,
        (Complex.exp (Complex.I * (((ξ * f x : ℝ) : ℂ))) - 1) ∂ν) =
      ∑ x ∈ f.range, ((((ν (B ∩ {y : ℝ | f y = x})).toReal : ℝ) : ℂ) *
        (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1)) := by sorry
