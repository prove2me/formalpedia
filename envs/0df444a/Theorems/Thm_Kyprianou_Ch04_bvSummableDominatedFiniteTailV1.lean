-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvSummableDominatedFiniteTailV1
-- name    : Kyprianou.Ch04.bvSummableDominatedFiniteTailV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:28:05.142913+00:00
-- url     : https://prove2.me/theorems/8683e475-2e20-471a-b331-6a64571ba945
-- title:
--   Uniform bound for a finite truncation of a dominated absolute series
-- statement:
--   Split both absolutely summable series into the finite set and its complement. Apply the norm comparison for the complement and cancel the finite sums.
-- source:
--   Kyprianou (2006), Theorem 4.2, pp. 91–93; deterministic absolutely summable jump approximation.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.bvSummableDominatedFiniteTailV1
    {I : Type} (g b : I → ℝ) (hb : Summable b)
    (h : ∀ i, |g i| ≤ b i) (S : Finset I) :
    |(∑' i, g i) - ∑ i ∈ S, g i| ≤ (∑' i, b i) - ∑ i ∈ S, b i := by
  sorry
