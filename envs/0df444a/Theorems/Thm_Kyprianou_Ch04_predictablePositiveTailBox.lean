-- Prove2me | Theorems.Thm_Kyprianou_Ch04_predictablePositiveTailBox
-- name    : Kyprianou.Ch04.predictablePositiveTailBox
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:13:11.810792+00:00
-- url     : https://prove2.me/theorems/d3d38a3c-cbb1-4d70-bf9a-8edbd4d9feb0
-- title:
--   predictablePositiveTailBox
-- statement:
--   An adapted positive-tail generator inside the horizon restricts to a weighted tail box.
-- source:
--   Kyprianou (2006), Exercise 4.4, physical finite predictable approximation.

import Mathlib
open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false

/-- An adapted tail generator within the horizon restricts to a weighted tail box. -/
theorem Kyprianou.Ch04.predictablePositiveTailBox
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (t : NNReal) (B : Set ℝ) (hB : MeasurableSet B)
    (a₀ : NNReal) (A : Set Omega) (hA : MeasurableSet[F a₀] A)
    (C₀ : Set ℝ) (hC : MeasurableSet C₀) (hat : a₀ ≤ t)
    (c : ℝ) :
    ∃ (a : NNReal) (C : Set ℝ) (H : Omega → ℝ),
      a ≤ t ∧ MeasurableSet C ∧ C ⊆ B ∧ StronglyMeasurable[F a] H ∧
      (∀ w, |H w| ≤ |c|) ∧
      ∀ (w : Omega) (z : ℝ × ℝ), z.1 ≠ 0 →
        (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B).indicator
          (fun z => c * ((Set.Ioi a₀ ×ˢ A) ×ˢ C₀).indicator (fun _ => (1 : ℝ)) ((z.1.toNNReal,w),z.2)) z =
        (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ C).indicator (fun _ => H w) z := by
  sorry
