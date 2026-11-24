-- Prove2me | Theorems.Thm_Kyprianou_Ch02_truncatedCumulativeAtomicSeriesAgreementV1
-- name    : Kyprianou.Ch02.truncatedCumulativeAtomicSeriesAgreementV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:23:13.245368+00:00
-- url     : https://prove2.me/theorems/a32004d6-516c-40ac-b637-bfd1569b9a69
-- title:
--   Local and globally truncated atomic sums agree on the truncation interval
-- statement:
--   Extend locally absolutely summable marks by zero outside the finite horizon. The extended marks are globally absolutely summable, and restricting the cumulative series to a smaller horizon recovers the original subtype series.
-- source:
--   Kyprianou (2006), Chapter 2 Lemma 2.12; local absolutely summable cumulative series and right continuity

import Mathlib
open MeasureTheory Set Function Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.truncatedCumulativeAtomicSeriesAgreementV1
    (g : ℝ≥0 → ℝ) (B : ℝ≥0)
    (hs : Summable (fun s : Ioc (0 : ℝ≥0) B => |g s|)) :
    Summable (fun u : ℝ≥0 => |(Ioc (0 : ℝ≥0) B).indicator g u|) ∧
      ∀ s : ℝ≥0, s ≤ B →
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
          (Ioc (0 : ℝ≥0) B).indicator g u else 0) =
          ∑' u : Ioc (0 : ℝ≥0) s, g u := by
  sorry
