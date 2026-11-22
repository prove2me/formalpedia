-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanRightMixingSetIntegralV1
-- name    : Kyprianou.Ch01.mckeanRightMixingSetIntegralV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T21:49:17.285411+00:00
-- url     : https://prove2.me/theorems/88c9a136-2265-418f-83c6-a9d5b5365874
-- title:
--   McKean independent-increment mixing: set-integral factorisation on adapted events
-- statement:
--   For every event measurable with respect to the past filtration, establish the equality of integrals obtained by conditioning a bounded payoff of adapted state plus independent increment. Prove via independence and product-measure Fubini. This is the substantive factorisation identity necessary for the exact right-continuous McKean conditional mixing theorem.
-- source:
--   Kyprianou (2006), Theorem 1.13, independence and conditional mixing.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanRightMixingSetIntegralV1
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (s : ℝ≥0)
    (Y Z : Ω → ℝ)
    (f : ℝ → ℝ) (K : ℝ)
    (hYm : @Measurable Ω ℝ (F s) inferInstance Y)
    (hZm : Measurable Z)
    (hf : Measurable f)
    (hBound : ∀ y, ‖f y‖ ≤ K)
    (hIndep : Indep (MeasurableSpace.comap Z inferInstance) (F s) P) :
    ∀ (A : Set Ω), MeasurableSet[F s] A →
      (∫ ω in A, f (Y ω + Z ω) ∂P) =
        (∫ ω in A, (∫ ξ, f (Y ω + Z ξ) ∂P) ∂P) := by sorry
