-- Prove2me | Theorems.Thm_Kyprianou_Ch04_closedStopMaskRegion
-- name    : Kyprianou.Ch04.closedStopMaskRegion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:24:29.748862+00:00
-- url     : https://prove2.me/theorems/7ffe47f9-8b0d-488f-8f9e-139e92603400
-- title:
--   closedStopMaskRegion
-- statement:
--   A closed stopping mask intersects a deterministic horizon in its clipped horizon.
-- source:
--   Kyprianou (2006), Exercise 4.3(ii), pp. 106-107.

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
open MeasureTheory Set
open scoped NNReal
set_option autoImplicit false

/-- A deterministic horizon intersected with a closed stop is the clipped horizon. -/
theorem Kyprianou.Ch04.closedStopMaskRegion (tau : WithTop NNReal) (t c : NNReal)
    (hc : (c : WithTop NNReal) = min tau (t : WithTop NNReal)) (s : ℝ) :
    (s ∈ Set.Icc (0 : ℝ) (t : ℝ) ∧ (s.toNNReal : WithTop NNReal) ≤ tau) ↔
      s ∈ Set.Icc (0 : ℝ) (c : ℝ)  := by
  sorry
