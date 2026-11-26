-- Prove2me | Theorems.Thm_Kyprianou_Ch04_predictableUnivTailBox
-- name    : Kyprianou.Ch04.predictableUnivTailBox
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:13:11.529822+00:00
-- url     : https://prove2.me/theorems/12c135fc-b48e-47af-8cd9-e1b886e77f51
-- title:
--   predictableUnivTailBox
-- statement:
--   The universal generator restricts to the positive-time band.
-- source:
--   Kyprianou (2006), Exercise 4.4, physical finite predictable approximation.

import Mathlib
open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false

/-- The universal generator restricts to the positive-time band. -/
theorem Kyprianou.Ch04.predictableUnivTailBox
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (t : NNReal) (B : Set ℝ) (hB : MeasurableSet B)
 (c : ℝ) :
    ∃ (a : NNReal) (C : Set ℝ) (H : Omega → ℝ),
      a ≤ t ∧ MeasurableSet C ∧ C ⊆ B ∧ StronglyMeasurable[F a] H ∧
      (∀ w, |H w| ≤ |c|) ∧
      ∀ (w : Omega) (z : ℝ × ℝ), z.1 ≠ 0 →
        (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B).indicator
          (fun z => c * ((Set.univ : Set ((NNReal × Omega) × ℝ))).indicator (fun _ => (1 : ℝ)) ((z.1.toNNReal,w),z.2)) z =
        (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ C).indicator (fun _ => H w) z := by
  sorry
