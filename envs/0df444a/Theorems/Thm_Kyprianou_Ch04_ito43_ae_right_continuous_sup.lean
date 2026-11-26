-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_ae_right_continuous_sup
-- name    : Kyprianou.Ch04.ito43_ae_right_continuous_sup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:21:27.842435+00:00
-- url     : https://prove2.me/theorems/f17d52fc-1b0f-5377-8e39-6778d1d03454
-- title:
--   Almost surely right continuous bounded errors have measurable absolute supremum
-- statement:
--   Use a countable dense time set with zero and the right endpoint. On the common path event the supremum over this set equals the full compact supremum.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_ae_right_continuous_sup {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (E : NNReal → Ω → ℝ) (T : NNReal)
    (hm : ∀ t, AEMeasurable (E t) P)
    (hr : ∀ᵐ w ∂P, (∀ t, ContinuousWithinAt (fun s => |E s w|) (Ici t) t) ∧
      BddAbove (range (fun t : Iic T => |E t w|))) :
    AEStronglyMeasurable (fun w => sSup (range (fun t : Iic T => |E t w|))) P := by sorry
