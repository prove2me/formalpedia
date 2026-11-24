-- Prove2me | Theorems.Thm_Kyprianou_Ch02_cadlagSignedJumpSeriesBorelFunctionalV1
-- name    : Kyprianou.Ch02.cadlagSignedJumpSeriesBorelFunctionalV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:12:54.926505+00:00
-- url     : https://prove2.me/theorems/2af9d33f-78e3-4ced-9225-5e82b7b2decb
-- title:
--   Measurable signed jump series on absolutely summable cadlag paths
-- statement:
--   Use measurable extended nonnegative positive and negative part jump series, take their toReal difference, and identify with the signed real sum when absolute summability holds. The functional must be globally measurable and agree on every qualifying cadlag path.
-- source:
--   Kyprianou (2006), Chapter 2 Lemma 2.12; generic marked jump enumeration and absolutely summable series

import Mathlib
open MeasureTheory Set Function Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.cadlagSignedJumpSeriesBorelFunctionalV1
    (T : ℝ≥0) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ,
      Measurable F ∧
      ∀ Y : ℝ≥0 → ℝ,
        (∀ t : ℝ≥0, ContinuousWithinAt Y (Set.Ici t) t) →
        (∀ t : ℝ≥0, 0 < t → ∃ l : ℝ, Tendsto Y (𝓝[<] t) (𝓝 l)) →
        Summable (fun s : Set.Ioc (0 : ℝ≥0) T =>
          |Y (s : ℝ≥0) - Function.leftLim Y (s : ℝ≥0)|) →
        F Y = ∑' s : Set.Ioc (0 : ℝ≥0) T,
          (Y (s : ℝ≥0) - Function.leftLim Y (s : ℝ≥0)) := by
  sorry
