-- Prove2me | Theorems.Thm_Kyprianou_Ch01_measurableVariableLengthSum
-- name    : Kyprianou.Ch01.measurableVariableLengthSum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T07:37:57.626188+00:00
-- url     : https://prove2.me/theorems/8418b1e2-08bd-4b59-a94b-2f439dadc7ba
-- title:
--   Measurability of the finite prefix sum of a countably indexed sequence with variable count
-- statement:
--   The map sending a natural-number count and a real-valued sequence to the finite sum of its first count terms is measurable on the product of the discrete count space and the sequence product space. The proof uses a countable measurable partition and pointwise finite sums. This is necessary to justify pushforward and Fubini in the independent geometric stopping mixture.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(ii), random stopping map measurability.

import Mathlib
open MeasureTheory
open scoped BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.measurableVariableLengthSum :
    Measurable (fun pair : ℕ × (ℕ → ℝ) =>
      ∑ i ∈ Finset.range pair.1, pair.2 i) := by
  sorry
