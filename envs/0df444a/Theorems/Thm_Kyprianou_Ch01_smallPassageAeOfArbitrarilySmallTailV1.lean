-- Prove2me | Theorems.Thm_Kyprianou_Ch01_smallPassageAeOfArbitrarilySmallTailV1
-- name    : Kyprianou.Ch01.smallPassageAeOfArbitrarilySmallTailV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T00:20:32.259189+00:00
-- url     : https://prove2.me/theorems/e7bb82bd-936b-4ae5-82d0-2e1567c8b216
-- title:
--   Arbitrarily small positive-barrier passage tails imply almost-sure small passage
-- statement:
--   Fix a time horizon epsilon and suppose positive spatial first-passage events T_s≥epsilon have arbitrarily small probability as s decreases. The event that no positive spatial level is crossed strictly before epsilon is contained in every tail event. Apply the general Proved nullEventOfArbitrarilySmallOuterBoundsV1 to this intersection event, then characterise the almost-sure complement with ae_iff. No measurability of the uncountable intersection is assumed, because the measure is an outer measure.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5, immediate crossing via shrinking spatial barrier probabilities.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.smallPassageAeOfArbitrarilySmallTailV1
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (ε : ℝ≥0)
    (hSmall : ∀ δ : ℝ, 0 < δ →
      ∃ s : ℝ≥0, 0 < s ∧
      (P {ω | (ε : WithTop ℝ≥0) ≤
         firstUpperPassage X (s : ℝ) ω}).toReal < δ) :
    ∀ᵐ ω ∂P, ∃ s : ℝ≥0, 0 < s ∧
      firstUpperPassage X (s : ℝ) ω <
        (ε : WithTop ℝ≥0) := by sorry
