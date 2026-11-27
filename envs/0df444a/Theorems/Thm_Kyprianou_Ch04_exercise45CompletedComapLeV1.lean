-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45CompletedComapLeV1
-- name    : Kyprianou.Ch04.exercise45CompletedComapLeV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-27T00:16:18.371797+00:00
-- url     : https://prove2.me/theorems/9dfce2bf-a89f-5342-b1eb-0c1e69a53631
-- title:
--   Completed sigma algebra contains the comap of an almost-sure version
-- statement:
--   The sigma algebra containing the comap of a variable and all subsets of measurable null sets also contains the comap of an almost-surely equal variable.
-- source:
--   Kyprianou Exercise 4.5, version normalisation

import Mathlib
open MeasureTheory Filter Set
set_option autoImplicit false

/-- Completion contains the comap of any a.e. equal version of a measurable variable. -/
theorem Kyprianou.Ch04.exercise45CompletedComapLeV1 {Ω : Type} [m : MeasurableSpace Ω] (P : Measure Ω)
    (f g : Ω → ℝ) (S : MeasurableSpace Ω)
    (hS : MeasurableSpace.comap f inferInstance ≤ S)
    (hNull : MeasurableSpace.generateFrom {A : Set Ω |
      ∃ N : Set Ω, @MeasurableSet Ω m N ∧ P N = 0 ∧ A ⊆ N} ≤ S)
    (hEq : f =ᵐ[P] g) :
    MeasurableSpace.comap g inferInstance ≤ S := by
  sorry
