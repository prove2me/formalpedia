-- Prove2me | Theorems.Thm_Kyprianou_Ch04_predictableBeyondHorizonTailBox
-- name    : Kyprianou.Ch04.predictableBeyondHorizonTailBox
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:13:11.560796+00:00
-- url     : https://prove2.me/theorems/18d36bd3-26a6-49e4-9c6d-e7e1ae86b1da
-- title:
--   predictableBeyondHorizonTailBox
-- statement:
--   A tail starting after the horizon has zero restricted contribution.
-- source:
--   Kyprianou (2006), Exercise 4.4, physical finite predictable approximation.

import Mathlib
open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false

/-- A tail starting after the horizon has zero restricted contribution. -/
theorem Kyprianou.Ch04.predictableBeyondHorizonTailBox
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (t : NNReal) (B : Set ℝ) (hB : MeasurableSet B)
    (a₀ : NNReal) (A : Set Omega) (C₀ : Set ℝ) (hat : ¬ a₀ ≤ t)
    (c : ℝ) :
    ∃ (a : NNReal) (C : Set ℝ) (H : Omega → ℝ),
      a ≤ t ∧ MeasurableSet C ∧ C ⊆ B ∧ StronglyMeasurable[F a] H ∧
      (∀ w, |H w| ≤ |c|) ∧
      ∀ (w : Omega) (z : ℝ × ℝ), z.1 ≠ 0 →
        (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B).indicator
          (fun z => c * ((Set.Ioi a₀ ×ˢ A) ×ˢ C₀).indicator (fun _ => (1 : ℝ)) ((z.1.toNNReal,w),z.2)) z =
        (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ C).indicator (fun _ => H w) z := by
  sorry
