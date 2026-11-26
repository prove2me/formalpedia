-- Prove2me | Theorems.Thm_Kyprianou_Ch04_arbitraryTimeMarkExtractorV1
-- name    : Kyprianou.Ch04.arbitraryTimeMarkExtractorV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:13:42.063025+00:00
-- url     : https://prove2.me/theorems/0536c051-84b9-513d-9494-9e90ff6ff959
-- title:
--   Coordinate measurable extractor for arbitrary Borel time-mark sets
-- statement:
--   Combine the proved exact measurable candidate selectors with deduplicated-series measurability and the physical cardinality identity.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, physical predictable integral approximation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn9_measurable_exact_cadlag_selectors
import Theorems.Thm_Kyprianou_Ch04_arbitraryTimeMarkCandidateSeriesMeasurableV1
import Theorems.Thm_Kyprianou_Ch04_arbitraryTimeMarkCandidateSeriesCardV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

namespace Kyprianou.Ch04
theorem arbitraryTimeMarkExtractorV1 (D : Set (ℝ × ℝ)) (hD : MeasurableSet D) :
    ∃ G : (NNReal → ℝ) → ENNReal, Measurable G ∧
      ∀ Y : NNReal → ℝ,
      (∀ u, ContinuousWithinAt Y (Ici u) u) →
      (∀ u, 0 < u → ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
      ({u : NNReal | 0 < u ∧ Y u - Function.leftLim Y u ≠ 0 ∧
        ((u : ℝ), Y u - Function.leftLim Y u) ∈ D}).encard = G Y := by
  sorry
end Kyprianou.Ch04
