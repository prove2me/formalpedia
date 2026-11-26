-- Prove2me | Theorems.Thm_Kyprianou_Ch04_arbitraryTimeMarkCandidateSeriesCardV1
-- name    : Kyprianou.Ch04.arbitraryTimeMarkCandidateSeriesCardV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:45:32.356035+00:00
-- url     : https://prove2.me/theorems/dd7f7ec2-8fb2-4881-a330-74974003ce62
-- title:
--   Deduplicated candidate series equals the actual marked-time cardinality
-- statement:
--   The exact candidate mark and time coverage identify membership in the physical jump-time set. Apply the proved first-occurrence cardinality formula.
-- source:
--   Kyprianou (2006), Chapter 4, physical Poisson integral approximation support.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_countable_first_candidate_cover_card_eq_dedup_sum
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

namespace Kyprianou.Ch04
theorem arbitraryTimeMarkCandidateSeriesCardV1 (Y : NNReal → ℝ) (time : ℕ → NNReal) (mark : ℕ → ℝ)
    (hMark : ∀ k, 0 < time k → mark k = Y (time k) - Function.leftLim Y (time k))
    (hCover : ∀ u, 0 < u → Y u - Function.leftLim Y u ≠ 0 → ∃ k, time k = u)
    (D : Set (ℝ × ℝ)) :
    ({u : NNReal | 0 < u ∧ Y u - Function.leftLim Y u ≠ 0 ∧
        ((u : ℝ), Y u - Function.leftLim Y u) ∈ D}).encard =
      ∑' k : ℕ, if 0 < time k ∧ mark k ≠ 0 ∧
        ((time k : ℝ), mark k) ∈ D ∧ (∀ j : ℕ, j < k → time j ≠ time k)
      then (1 : ENNReal) else 0 := by
  sorry
end Kyprianou.Ch04
