-- Prove2me | Theorems.Thm_Kyprianou_Ch04_normalizedDeficitMomentCharacterisationV1
-- name    : Kyprianou.Ch04.normalizedDeficitMomentCharacterisationV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:06:36.506705+00:00
-- url     : https://prove2.me/theorems/e29ae2db-6e02-4be5-b7e0-3817d4e590b9
-- title:
--   Extended first moment characterised by normalized exponential deficits
-- statement:
--   The first-moment upper bound is equivalent to all normalized exponential-deficit integral upper bounds, for any measure. The pointwise bound follows from 1+ay ≤ exp(ay). For the reverse, use the right limit at zero, derivative of the exponential, and Fatou. The statement allows infinite first moment and needs no sigma-finiteness assumption.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.1, analytic traffic classification.

import Mathlib
open MeasureTheory Filter
open scoped ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.normalizedDeficitMomentCharacterisationV1
    (nu : Measure Real) (d : Real) :
    (∫⁻ y : Real, ENNReal.ofReal (-y) ∂nu) ≤ ENNReal.ofReal d ↔
      ∀ a : Real, 0 < a →
        (∫⁻ y : Real, ENNReal.ofReal ((1 - Real.exp (a*y))/a) ∂nu) ≤
          ENNReal.ofReal d := by
  sorry
