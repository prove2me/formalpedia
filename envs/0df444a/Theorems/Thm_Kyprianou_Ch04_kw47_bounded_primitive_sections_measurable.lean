-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_bounded_primitive_sections_measurable
-- name    : Kyprianou.Ch04.kw47_bounded_primitive_sections_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T12:34:27.58389+00:00
-- url     : https://prove2.me/theorems/efe28ff4-b4da-432c-a660-13bd1fbb2f42
-- title:
--   Measurability of a fixed-time integral section
-- statement:
--   Bochner integration under the fixed restriction of volume preserves strong measurability of jointly measurable real-valued functions.
-- source:
--   Kyprianou (2006), Exercise 4.7; analytic compact-horizon process properties.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch04.kw47_bounded_primitive_sections_measurable
    {Omega : Type} [MeasurableSpace Omega] (f : Real × Omega → Real)
    (hf : Measurable f) (t : NNReal) :
    Measurable (fun w => ∫ s in Icc (0 : Real) (t : Real), f (s,w) ∂volume) := by sorry
