-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineQuotientDerivative
-- name    : Kyprianou.Ch01.stableAlphaOneCosineQuotientDerivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T09:02:43.702395+00:00
-- url     : https://prove2.me/theorems/72605bc4-55ff-4550-bf24-71a214dd75d9
-- title:
--   Cosine quotient derivative identity for the index-one stable integral
-- statement:
--   At every nonzero real r, the derivative of (1−cos r)/r is sin r/r−(1−cos r)/r². This is the exact integration-by-parts identity needed to reduce the stable alpha-one cosine integral to the classical Dirichlet sine integral, with no changes to the original integrand.
-- source:
--   Kyprianou (2006), Chapter 1, α=1 stable cosine Lévy exponent.

import Mathlib
open MeasureTheory Filter Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneCosineQuotientDerivative
    (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun x : ℝ => (1 - Real.cos x) / x)
      (Real.sin r / r - (1 - Real.cos r) / r ^ 2) r := by
  sorry
