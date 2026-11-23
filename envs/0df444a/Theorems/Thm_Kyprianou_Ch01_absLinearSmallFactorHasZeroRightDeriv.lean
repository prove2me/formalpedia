-- Prove2me | Theorems.Thm_Kyprianou_Ch01_absLinearSmallFactorHasZeroRightDeriv
-- name    : Kyprianou.Ch01.absLinearSmallFactorHasZeroRightDeriv
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T12:44:05.057965+00:00
-- url     : https://prove2.me/theorems/fd185325-c440-450d-b0ca-0c1d375acce8
-- title:
--   Absolute linear-small-factor bound implies zero right derivative
-- statement:
--   If |f(t)| is bounded by c*t*h(t) for nonnegative t and h(t) tends to zero as t approaches zero from the right, then f has right derivative zero. The bound at t=0 forces f(0)=0. Divide by t>0 and squeeze the slope using the factor h(t).
-- source:
--   Mathlib one-sided derivative slope criterion and squeeze-zero-norm lemma

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.SetSemiring
open MeasureTheory Filter Set
set_option autoImplicit false

theorem Kyprianou.Ch01.absLinearSmallFactorHasZeroRightDeriv
    (f h : ℝ → ℝ) (c : ℝ)
    (hSmall : Tendsto h
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hBound : ∀ t : ℝ, 0 ≤ t → |f t| ≤ c * t * h t) :
    HasDerivWithinAt f 0 (Set.Ici 0) 0 := by
  sorry
