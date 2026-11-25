-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvFiniteTruncationLeftLimitV1
-- name    : Kyprianou.Ch04.bvFiniteTruncationLeftLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:28:06.090852+00:00
-- url     : https://prove2.me/theorems/0cd9626f-07e9-4582-80a2-94c53fb3c58c
-- title:
--   Explicit left limit of a finite-jump truncation
-- statement:
--   For each retained jump the indicator is eventually constant in the left neighbourhood. Pass to the finite sum and add the continuous affine drift.
-- source:
--   Kyprianou (2006), Theorem 4.2, pp. 91–93; deterministic absolutely summable jump approximation.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.bvFiniteTruncationLeftLimitV1
    {I : Type} (τ : I → NNReal) (j : I → ℝ) (a c : ℝ)
    (S : Finset I) (u : NNReal) (hu : 0 < u) :
    Tendsto (fun v : NNReal => a + c * (v : ℝ) +
      ∑ s ∈ S, if τ s ≤ v then j s else 0)
      (nhdsWithin u (Set.Iio u))
      (nhds (a + c * (u : ℝ) + ∑ s ∈ S, if τ s < u then j s else 0)) := by
  sorry
