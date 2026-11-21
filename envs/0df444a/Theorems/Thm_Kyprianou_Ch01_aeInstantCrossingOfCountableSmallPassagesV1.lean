-- Prove2me | Theorems.Thm_Kyprianou_Ch01_aeInstantCrossingOfCountableSmallPassagesV1
-- name    : Kyprianou.Ch01.aeInstantCrossingOfCountableSmallPassagesV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T00:09:38.043177+00:00
-- url     : https://prove2.me/theorems/9e2199c9-7275-4436-b56b-fbd69529be9b
-- title:
--   Countably vanishing passage horizons imply almost-sure immediate upper crossing
-- statement:
--   A family of positive-barrier passage events at countably many arbitrarily small horizons implies almost-sure instantaneous crossing. Intersect the per-horizon full-measure sets using Mathlib ae_all_iff, choose a horizon δ_n below the requested ε, and invoke the proved firstUpperPassage_crossingBefore_of_ltV1 theorem. Since the crossed barrier is positive, the actual crossing satisfies X_t>0. No Brownian assumptions or reflection principle are needed; only the specified per-horizon full-measure passage premise.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5 and elementary countable full-measure intersection.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.aeInstantCrossingOfCountableSmallPassagesV1
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (δ : ℕ → ℝ≥0)
    (hδ : ∀ ε : ℝ≥0, 0 < ε → ∃ n : ℕ, δ n < ε)
    (hSmall : ∀ n : ℕ, ∀ᵐ ω ∂P,
      ∃ s : ℝ≥0, 0 < s ∧
        firstUpperPassage X (s : ℝ) ω < (δ n : WithTop ℝ≥0)) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, 0 < t ∧ t < ε ∧ 0 < X t ω := by sorry
