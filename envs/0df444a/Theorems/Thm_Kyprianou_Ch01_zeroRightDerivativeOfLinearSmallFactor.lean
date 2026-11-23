-- Prove2me | Theorems.Thm_Kyprianou_Ch01_zeroRightDerivativeOfLinearSmallFactor
-- name    : Kyprianou.Ch01.zeroRightDerivativeOfLinearSmallFactor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T12:13:45.976951+00:00
-- url     : https://prove2.me/theorems/70c0df9e-2322-4804-bdac-f60c8a56fd53
-- title:
--   Right derivative zero from a linear upper bound times a vanishing factor
-- statement:
--   If 0≤f(t)≤c*t*h(t) for nonnegative times and h(t)→0 as t decreases to zero, then the right derivative of f at zero vanishes. Use the slope characterisation of HasDerivWithinAt and the filter squeeze theorem.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.zeroRightDerivativeOfLinearSmallFactor
    (f h : ℝ → ℝ) (c : ℝ)
    (hSmall : Tendsto h
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hBound : ∀ t : ℝ, 0 ≤ t →
      0 ≤ f t ∧ f t ≤ c * t * h t) :
    HasDerivWithinAt f 0 (Set.Ici 0) 0 := by
  sorry
