-- Prove2me | Theorems.Thm_Kyprianou_Ch04_arbitraryTimeMarkCandidateSeriesMeasurableV1
-- name    : Kyprianou.Ch04.arbitraryTimeMarkCandidateSeriesMeasurableV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T00:45:18.67284+00:00
-- url     : https://prove2.me/theorems/8697c3f1-968d-5e5d-b055-93c2b29ef3eb
-- title:
--   Measurability of the deduplicated candidate series for an arbitrary Borel time-mark set
-- statement:
--   The summand is a measurable indicator of the intersection of the positive-time, nonzero-mark, Borel membership and countably many first-occurrence conditions. Nonnegative countable summation preserves measurability.
-- source:
--   Kyprianou (2006), Chapter 4, physical Poisson integral approximation support.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

namespace Kyprianou.Ch04
theorem arbitraryTimeMarkCandidateSeriesMeasurableV1 (time : ℕ → (NNReal → ℝ) → NNReal)
    (mark : ℕ → (NNReal → ℝ) → ℝ)
    (ht : ∀ k, Measurable (time k)) (hm : ∀ k, Measurable (mark k))
    (D : Set (ℝ × ℝ)) (hD : MeasurableSet D) :
    Measurable (fun Y : NNReal → ℝ => ∑' k : ℕ,
      if 0 < time k Y ∧ mark k Y ≠ 0 ∧
        ((time k Y : ℝ), mark k Y) ∈ D ∧
        (∀ j : ℕ, j < k → time j Y ≠ time k Y)
      then (1 : ENNReal) else 0) := by
  sorry
end Kyprianou.Ch04
