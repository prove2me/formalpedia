-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42SupremumIncrementBoundsV1
-- name    : Kyprianou.Ch04.exercise42SupremumIncrementBoundsV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T08:15:06.296877+00:00
-- url     : https://prove2.me/theorems/89fef271-0580-490f-b392-f0bf4cf6cfff
-- title:
--   Positive-drift residual gives Lipschitz running supremum
-- statement:
--   Compare all earlier and later candidate record times using the monotone drift residual; the nonnegative running supremum starts at zero and its increments are bounded by the linear drift.
-- source:
--   Kyprianou (2006), Exercise 4.2, p. 106 and solution p. 317; deterministic and source-law reduction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open ProbabilityTheory Set Topology
open scoped Topology

theorem Kyprianou.Ch04.exercise42SupremumIncrementBoundsV1
    (X : NNReal → Real) (c : Real) (hc : 0 < c)
    (hzero : X 0 = 0)
    (hMon : Monotone (fun t : NNReal => (t : Real) * c - X t)) :
    let U : NNReal → Real := fun t => sSup (X '' Set.Iic t)
    U 0 = 0 ∧ (∀ t, 0 ≤ U t) ∧
    (∀ s t : NNReal, s ≤ t →
      0 ≤ U t - U s ∧ U t - U s ≤ c * ((t : Real) - (s : Real))) ∧
    LipschitzWith c.toNNReal U := by
  sorry
