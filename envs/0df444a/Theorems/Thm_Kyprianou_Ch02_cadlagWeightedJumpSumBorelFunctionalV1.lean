-- Prove2me | Theorems.Thm_Kyprianou_Ch02_cadlagWeightedJumpSumBorelFunctionalV1
-- name    : Kyprianou.Ch02.cadlagWeightedJumpSumBorelFunctionalV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:12:57.584515+00:00
-- url     : https://prove2.me/theorems/b0a2ba29-cbab-464f-aff2-efa128c80560
-- title:
--   Measurable weighted extended jump series of a cadlag path
-- statement:
--   Generalise the proved small-jump measurable functional to arbitrary measurable nonnegative mark weights vanishing at zero. Use the existing public Borel weighted marked-count integral, identify with the time-subtype series by lintegral_map, lintegral_count and tsum_subtype.
-- source:
--   Kyprianou (2006), Chapter 2 Lemma 2.12; generic marked jump enumeration and absolutely summable series

import Mathlib
open MeasureTheory Set Function Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.cadlagWeightedJumpSumBorelFunctionalV1
    (T : ℝ≥0) (g : ℝ → ℝ≥0∞) (hg : Measurable g) (hg0 : g 0 = 0) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable F ∧
      ∀ Y : ℝ≥0 → ℝ,
        (∀ t : ℝ≥0, ContinuousWithinAt Y (Set.Ici t) t) →
        (∀ t : ℝ≥0, 0 < t → ∃ l : ℝ, Tendsto Y (𝓝[<] t) (𝓝 l)) →
        F Y = ∑' s : Set.Ioc (0 : ℝ≥0) T,
          g (Y (s : ℝ≥0) - Function.leftLim Y (s : ℝ≥0)) := by
  sorry
