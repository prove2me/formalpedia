-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvFiniteTruncationJumpDifferenceV1
-- name    : Kyprianou.Ch04.bvFiniteTruncationJumpDifferenceV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:31:37.712316+00:00
-- url     : https://prove2.me/theorems/1af097ff-473b-47c2-80cf-f75007f8e840
-- title:
--   Exact jump of a finite truncation at an indexed time
-- statement:
--   The difference between the weak and strict time indicators selects precisely the indexed jump, and injectivity rules out any other index at that time.
-- source:
--   Kyprianou (2006), Theorem 4.2, pp. 91–93; compact deterministic estimates.

import Mathlib
open MeasureTheory Filter Set
open scoped Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.bvFiniteTruncationJumpDifferenceV1
    {I : Type} [DecidableEq I]
    (τ : I → ℝ) (hτ : Function.Injective τ) (j : I → ℝ)
    (a d : ℝ) (S : Finset I) (s : I) :
    (a+d*τ s+∑ i ∈ S, if τ i ≤ τ s then j i else 0) -
      (a+d*τ s+∑ i ∈ S, if τ i < τ s then j i else 0) =
        if s ∈ S then j s else 0 := by
  sorry
