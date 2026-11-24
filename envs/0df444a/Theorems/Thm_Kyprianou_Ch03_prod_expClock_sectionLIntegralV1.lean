-- Prove2me | Theorems.Thm_Kyprianou_Ch03_prod_expClock_sectionLIntegralV1
-- name    : Kyprianou.Ch03.prod_expClock_sectionLIntegralV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T16:46:07.889839+00:00
-- url     : https://prove2.me/theorems/c9961a89-6523-478b-8c2d-ea703c7d31cf
-- title:
--   Product measure of an arbitrary clock above a measurable extended threshold
-- statement:
--   Use the rational separator to write the event as a countable union of rectangles with measurable left sides, and use the proved countable-rectangle product measure theorem. Sections are the same countable union of right sides.
-- source:
--   Kyprianou (2006), Exercise 3.6; faithful auxiliary reduction of e7615c25-61ff-4f34-bf1a-1f06850e5e0e.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.prod_expClock_sectionLIntegralV1
    {Omega OmegaE : Type} [MeasurableSpace Omega] [MeasurableSpace OmegaE]
    (P : Measure Omega) (Q : Measure OmegaE)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (tau : Omega → WithTop NNReal) (htau : Measurable tau)
    (e : OmegaE → NNReal) :
    (P.prod Q) {z : Omega × OmegaE | tau z.1 < (e z.2 : WithTop NNReal)} =
      ∫⁻ w, Q {z : OmegaE | tau w < (e z : WithTop NNReal)} ∂P := by sorry
