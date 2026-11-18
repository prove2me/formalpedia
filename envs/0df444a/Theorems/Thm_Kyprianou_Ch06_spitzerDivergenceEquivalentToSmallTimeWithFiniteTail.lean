-- Prove2me | Theorems.Thm_Kyprianou_Ch06_spitzerDivergenceEquivalentToSmallTimeWithFiniteTail
-- name    : Kyprianou.Ch06.spitzerDivergenceEquivalentToSmallTimeWithFiniteTail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:19:40.91521+00:00
-- url     : https://prove2.me/theorems/cd319609-eeb9-4f70-9243-4c9d5ccf60ee
-- title:
--   Spitzer Exercise 6.8: full positive-time divergence equivalent to small-time divergence when tail is finite
-- statement:
--   For any extended-nonnegative measurable-time integrand, if its integral over times greater than one is finite, then its integral over all positive times diverges exactly when its integral over (0,1] diverges. This establishes the analytic truncation needed in both strict and non-strict Spitzer regularity criteria.
-- source:
--   Kyprianou (2006), Exercise 6.8(i)-(ii) solution, printed pp.333–334, comparison of full-time and small-time occupation integrals.

import Mathlib
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.spitzerDivergenceEquivalentToSmallTimeWithFiniteTail
    (f : Real → ENNReal)
    (hTail : (∫⁻ t in Set.Ioi (1 : Real), f t ∂volume) < ⊤) :
    (∫⁻ t in Set.Ioi (0 : Real), f t ∂volume) = ⊤ ↔
      (∫⁻ t in Set.Ioc (0 : Real) 1, f t ∂volume) = ⊤ := by sorry
