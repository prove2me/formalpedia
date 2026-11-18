-- Prove2me | Theorems.Thm_Kyprianou_Ch06_spitzerDiscountedTailFiniteENNReal
-- name    : Kyprianou.Ch06.spitzerDiscountedTailFiniteENNReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T07:51:27.788893+00:00
-- url     : https://prove2.me/theorems/e840721a-2da3-48fa-b38b-16804ceb0dbf
-- title:
--   Spitzer Exercise 6.8: exponential occupation tail finite as an ENNReal integral
-- statement:
--   For a positive discount and a measurable occupation probability factor f in [0,1] for all t>1, the ENNReal Lebesgue integral of exp(-pt)f(t)/t on (1,∞) is finite. Converts the already Proved real integrability estimate to the exact ENNReal divergence framework used by both strict and non-strict Spitzer regularity criteria in Exercise 6.8.
-- source:
--   Kyprianou (2006), Exercise 6.8(i)-(ii) solution, printed pp.333–334.

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_spitzerExponentialOccupationTailIntegrable
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.spitzerDiscountedTailFiniteENNReal
    (p : Real) (hp : 0 < p)
    (f : Real → Real) (hf : Measurable f)
    (hfBound : ∀ t ∈ Set.Ioi (1 : Real), 0 ≤ f t ∧ f t ≤ 1) :
    (∫⁻ t in Set.Ioi (1 : Real),
      ENNReal.ofReal (Real.exp (-p * t) * f t / t) ∂volume) < ⊤ := by sorry
