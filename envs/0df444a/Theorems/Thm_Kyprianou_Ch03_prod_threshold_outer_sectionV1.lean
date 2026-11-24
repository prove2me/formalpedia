-- Prove2me | Theorems.Thm_Kyprianou_Ch03_prod_threshold_outer_sectionV1
-- name    : Kyprianou.Ch03.prod_threshold_outer_sectionV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T11:03:45.673836+00:00
-- url     : https://prove2.me/theorems/a036dd95-b0fe-4391-b23d-6894b346aa7d
-- title:
--   Product measure of an extended threshold comparison by outer-measure sections
-- statement:
--   Use the dense rational cuts between a finite threshold and the clock to express the strict comparison as a countable union of rectangles with measurable left factors. Apply the countable rectangle outer-measure identity; the right sections are exactly the strict comparison events. No clock measurability is assumed.
-- source:
--   Measure-theoretic auxiliary for Kyprianou (2006), Chapter 3, Exercise 3.6.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.prod_threshold_outer_sectionV1
    {Omega OmegaE : Type} [MeasurableSpace Omega] [MeasurableSpace OmegaE]
    (P : Measure Omega) (Q : Measure OmegaE)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (tau : Omega → WithTop NNReal) (htau : Measurable tau)
    (e : OmegaE → NNReal) :
    (P.prod Q) {z : Omega × OmegaE | tau z.1 < (e z.2 : WithTop NNReal)} =
      ∫⁻ w, Q {z : OmegaE | tau w < (e z : WithTop NNReal)} ∂P := by sorry
