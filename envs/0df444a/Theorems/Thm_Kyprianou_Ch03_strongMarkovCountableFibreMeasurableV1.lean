-- Prove2me | Theorems.Thm_Kyprianou_Ch03_strongMarkovCountableFibreMeasurableV1
-- name    : Kyprianou.Ch03.strongMarkovCountableFibreMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:05:57.630212+00:00
-- url     : https://prove2.me/theorems/7d8283c9-c53f-4397-a887-426474327188
-- title:
--   Countable-fibre measurable gluing
-- statement:
--   Express the preimage of a measurable set as a countable union over the range of T, intersecting each fibre with the corresponding measurable preimage.
-- source:
--   Kyprianou (2006), Theorem 3.1; countable-grid restricted law ce10a41b-6699-4acd-b73c-5cedfb05d77b.

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.strongMarkovCountableFibreMeasurableV1
    {Omega I E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (T : Omega → I) (hCount : Countable (Set.range T))
    (hFib : ∀ i : I, MeasurableSet {w | T w = i})
    (Y : I → Omega → E) (hY : ∀ i, Measurable (Y i)) :
    Measurable (fun w => Y (T w) w) := by
  sorry
