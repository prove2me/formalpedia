-- Prove2me | Theorems.Thm_Kyprianou_Ch04_predictableInitialTailBox
-- name    : Kyprianou.Ch04.predictableInitialTailBox
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:13:11.072045+00:00
-- url     : https://prove2.me/theorems/15233008-f465-4b0e-90ed-2e525b8d8e5f
-- title:
--   predictableInitialTailBox
-- statement:
--   The time-zero generator vanishes away from time zero.
-- source:
--   Kyprianou (2006), Exercise 4.4, physical finite predictable approximation.

import Mathlib
open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false

/-- The time-zero generator vanishes away from time zero. -/
theorem Kyprianou.Ch04.predictableInitialTailBox
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (t : NNReal) (B : Set ℝ) (hB : MeasurableSet B)
    (A : Set Omega) (C₀ : Set ℝ)
    (c : ℝ) :
    ∃ (a : NNReal) (C : Set ℝ) (H : Omega → ℝ),
      a ≤ t ∧ MeasurableSet C ∧ C ⊆ B ∧ StronglyMeasurable[F a] H ∧
      (∀ w, |H w| ≤ |c|) ∧
      ∀ (w : Omega) (z : ℝ × ℝ), z.1 ≠ 0 →
        (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B).indicator
          (fun z => c * ((({⊥} : Set NNReal) ×ˢ A) ×ˢ C₀).indicator (fun _ => (1 : ℝ)) ((z.1.toNNReal,w),z.2)) z =
        (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ C).indicator (fun _ => H w) z := by
  sorry
