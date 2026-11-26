-- Prove2me | Theorems.Thm_Kyprianou_Ch04_predictableGeneratorTailBox
-- name    : Kyprianou.Ch04.predictableGeneratorTailBox
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:56:59.859781+00:00
-- url     : https://prove2.me/theorems/a9391bac-86e4-4d12-b186-5fec65ff0eef
-- title:
--   Predictable generator restricted to finite tail box
-- statement:
--   Away from time zero a finite-horizon restriction of a marked predictable generator is a weighted tail rectangle with a bounded coefficient measurable at its lower endpoint.
-- source:
--   Kyprianou (2006), Exercise 4.4, predictable simple approximation.

import Mathlib
open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false

/-- Restrict one marked predictable generator to a positive finite horizon. -/
theorem Kyprianou.Ch04.predictableGeneratorTailBox
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (t : NNReal) (B : Set ℝ) (hB : MeasurableSet B)
    (D : Set ((NNReal × Omega) × ℝ))
    (hD : D ∈ insert Set.univ (insert ∅
      (Set.image2 (· ×ˢ ·)
        {S : Set (NNReal × Omega) |
          (∃ A : Set Omega, MeasurableSet[F ⊥] A ∧ S = ({⊥} ×ˢ A)) ∨
          (∃ a : NNReal, ∃ A : Set Omega, MeasurableSet[F a] A ∧ S = (Set.Ioi a ×ˢ A))}
        {C : Set ℝ | MeasurableSet C}))) (c : ℝ) :
    ∃ (a : NNReal) (C : Set ℝ) (H : Omega → ℝ),
      a ≤ t ∧ MeasurableSet C ∧ C ⊆ B ∧ StronglyMeasurable[F a] H ∧
      (∀ w, |H w| ≤ |c|) ∧
      ∀ (w : Omega) (z : ℝ × ℝ), z.1 ≠ 0 →
        (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B).indicator
          (fun z => c * D.indicator (fun _ => (1 : ℝ)) ((z.1.toNNReal,w),z.2)) z =
        (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ C).indicator (fun _ => H w) z := by
  sorry
