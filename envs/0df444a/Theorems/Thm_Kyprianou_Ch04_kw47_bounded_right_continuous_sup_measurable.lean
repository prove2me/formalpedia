-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_bounded_right_continuous_sup_measurable
-- name    : Kyprianou.Ch04.kw47_bounded_right_continuous_sup_measurable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T12:34:36.80873+00:00
-- url     : https://prove2.me/theorems/82aba6e4-d780-42ca-ab22-a0e6bc2f3d45
-- title:
--   Countable dense supremum of a bounded right-continuous process
-- statement:
--   Use a countable dense time set containing zero and include the right endpoint. The supremum is a countable supremum of measurable sections.
-- source:
--   Kyprianou (2006), Exercise 4.7; analytic compact-horizon process properties.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_dense_timeSup_with_endpoint
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch04.kw47_bounded_right_continuous_sup_measurable
    {Omega : Type} [MeasurableSpace Omega] (f : NNReal → Omega → Real)
    (hm : ∀ t, Measurable (f t))
    (hr : ∀ w t, ContinuousWithinAt (fun s => f s w) (Ici t) t)
    (t : NNReal)
    (hb : ∀ w, BddAbove ((fun s => f s w) '' Iic t)) :
    Measurable (fun w => sSup ((fun s => f s w) '' Iic t)) := by sorry
