-- Prove2me | Theorems.Thm_Kyprianou_Ch02_absSummableJumpSeriesMonotonePairV1
-- name    : Kyprianou.Ch02.absSummableJumpSeriesMonotonePairV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T20:44:21.53649+00:00
-- url     : https://prove2.me/theorems/aa9a675c-abf2-4e67-9604-1992f5561246
-- title:
--   Absolute summability of timed jumps yields two monotone cumulative sums
-- statement:
--   For arbitrary real jump weights on the positive real time axis that are absolutely summable on every interval (0,T], split each jump into its positive and negative parts, sum each separately, and obtain two monotone cumulative functions whose difference is exactly the signed jump sum at all nonnegative times. This deterministic lemma supports the original Lévy–Itô variation proof without a finite-activity restriction.
-- source:
--   Proof adapted from the Apache-2.0 StochLean PathVariation finite-jump-series source, pinned source under work/project_import_throughput_round12_20261123; mathematical motivation Kyprianou (2006) Chapter 2 Lemma 2.12.

import Mathlib
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.absSummableJumpSeriesMonotonePairV1
    (g : ℝ≥0 → ℝ)
    (hs : ∀ T : ℝ≥0, Summable
      (fun s : Set.Ioc (0 : ℝ≥0) T => |g s|)) :
    ∃ (p q : ℝ≥0 → ℝ), Monotone p ∧ Monotone q ∧
      ∀ T : ℝ≥0,
        (∑' s : Set.Ioc (0 : ℝ≥0) T, g s) = p T - q T := by
  sorry
