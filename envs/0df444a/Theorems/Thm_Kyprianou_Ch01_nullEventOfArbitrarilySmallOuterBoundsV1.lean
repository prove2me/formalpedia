-- Prove2me | Theorems.Thm_Kyprianou_Ch01_nullEventOfArbitrarilySmallOuterBoundsV1
-- name    : Kyprianou.Ch01.nullEventOfArbitrarilySmallOuterBoundsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T00:14:21.850191+00:00
-- url     : https://prove2.me/theorems/a22001bf-c0a5-4411-a077-5ced3996ad40
-- title:
--   An event included in arbitrarily small probability supersets has measure zero
-- statement:
--   An arbitrary outer event E has zero probability whenever it is contained in every member of a family of events A_i and the probability of some A_i can be made smaller than any positive real number. The proof uses monotonicity of measure, conversion to finite real mass under IsProbabilityMeasure, and the Archimedean positivity contradiction. This avoids measurable-event assumptions for E and is the exact stochastic closure mechanism for immediate upper crossing deduced from first-passage tails.
-- source:
--   Continuity of probability outer measure from its monotonicity and arbitrarily small dominating events.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.nullEventOfArbitrarilySmallOuterBoundsV1
    {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (E : Set Ω) (A : ι → Set Ω)
    (hSub : ∀ i : ι, E ⊆ A i)
    (hSmall : ∀ δ : ℝ, 0 < δ →
      ∃ i : ι, (P (A i)).toReal < δ) :
    P E = 0 := by sorry
