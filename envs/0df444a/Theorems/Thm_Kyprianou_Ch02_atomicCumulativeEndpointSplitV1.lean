-- Prove2me | Theorems.Thm_Kyprianou_Ch02_atomicCumulativeEndpointSplitV1
-- name    : Kyprianou.Ch02.atomicCumulativeEndpointSplitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:26:54.727492+00:00
-- url     : https://prove2.me/theorems/855153cb-054c-46f8-a948-91448f88f605
-- title:
--   Absolutely summable atomic cumulative series splits at its endpoint
-- statement:
--   For globally absolutely summable real marks at nonnegative times, the cumulative sum through a positive endpoint equals the strict-past sum plus the endpoint mark. This isolates the endpoint calculation in locallySummableTimeRepresentationActualJumpsV2.
-- source:
--   Kyprianou (2006), Chapter 2 Lemma 2.12, deterministic jump-series representation

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Instances.NNReal.Lemmas
open Set Filter Topology
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.atomicCumulativeEndpointSplitV1
    (F : ℝ≥0 → ℝ) (hS : Summable (fun u : ℝ≥0 => |F u|))
    (t : ℝ≥0) (ht : 0 < t) :
    (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then F u else 0) =
      (∑' u : ℝ≥0, if 0 < u ∧ u < t then F u else 0) + F t := by
  sorry
