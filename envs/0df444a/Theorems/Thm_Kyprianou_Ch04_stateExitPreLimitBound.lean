-- Prove2me | Theorems.Thm_Kyprianou_Ch04_stateExitPreLimitBound
-- name    : Kyprianou.Ch04.stateExitPreLimitBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:39:02.483409+00:00
-- url     : https://prove2.me/theorems/9c9627a2-b3a0-40e3-8573-7711226da77a
-- title:
--   stateExitPreLimitBound
-- statement:
--   A first open spatial exit bounds every earlier state and the left limit at exit.
-- source:
--   Kyprianou (2006), Exercise 4.3(iii).

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- A first open spatial exit bounds every earlier state and the left limit at exit. -/
theorem Kyprianou.Ch04.stateExitPreLimitBound (Y L : NNReal → ℝ) (n : ℝ)
    (hl : ∀ t : NNReal, 0 < t → Tendsto Y (nhdsWithin t (Iio t)) (nhds (L t))) :
    let tau : WithTop NNReal := sInf {v : WithTop NNReal |
      ∃ u : NNReal, v = ↑u ∧ n < |Y u|}
    (∀ u : NNReal, (u : WithTop NNReal) < tau → |Y u| ≤ n) ∧
    (∀ t : NNReal, 0 < t → (t : WithTop NNReal) ≤ tau → |L t| ≤ n) := by
  sorry
