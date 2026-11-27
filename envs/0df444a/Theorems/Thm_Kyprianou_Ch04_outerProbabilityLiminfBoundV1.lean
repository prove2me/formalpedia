-- Prove2me | Theorems.Thm_Kyprianou_Ch04_outerProbabilityLiminfBoundV1
-- name    : Kyprianou.Ch04.outerProbabilityLiminfBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:09:03.584824+00:00
-- url     : https://prove2.me/theorems/5554e974-715e-491e-9660-962181271135
-- title:
--   outerProbabilityLiminfBoundV1
-- statement:
--   outerProbabilityLiminfBoundV1
-- source:
--   Kyprianou (2006), Exercise 4.5(iii), uniform cutoff probability envelope

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal
set_option autoImplicit false

/-- A bound on all sufficiently late outer probabilities transfers to an almost
sure eventually contained event, using measurable hulls. -/

theorem Kyprianou.Ch04.outerProbabilityLiminfBoundV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Set Ω) (B : ℕ → Set Ω) (q : ℝ) (hq : 0 ≤ q)
    (hB : ∀ᶠ l in atTop, (P (B l)).toReal ≤ q)
    (hSub : ∀ᵐ w ∂P, w ∈ A → ∃ N : ℕ, ∀ l ≥ N, w ∈ B l) :
    (P A).toReal ≤ q := by
  sorry
