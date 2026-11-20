-- Prove2me | Theorems.Thm_Kyprianou_Ch01_finitePositiveSupportDiscountIntegrable
-- name    : Kyprianou.Ch01.finitePositiveSupportDiscountIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T18:54:07.046834+00:00
-- url     : https://prove2.me/theorems/d5635569-1a79-4d93-8276-b4ce783e7614
-- title:
--   Discount exponential is integrable for a finite measure supported on nonnegative reals
-- statement:
--   If mu has finite mass and is almost everywhere supported on x>=0, exp(-q*x) is mu-integrable for every q>=0. Uses norm bound <=1 and Integrable.of_bound. This is a genuine generalisation of the inverse Gaussian discount-integrability obligation.
-- source:
--   Kyprianou (2006) Exercise 1.6(iii), discounted inverse Gaussian passage-time density.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.finitePositiveSupportDiscountIntegrable
    (mu : Measure ℝ)
    (hfin : mu Set.univ < ∞)
    (hsupp : ∀ᵐ x ∂mu, 0 ≤ x)
    (q : ℝ) (hq : 0 ≤ q) :
    Integrable (fun x : ℝ => Real.exp (-q * x)) mu := by sorry
