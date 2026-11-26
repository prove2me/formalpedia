-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteGeneratorSumTailRepresentation
-- name    : Kyprianou.Ch04.finiteGeneratorSumTailRepresentation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:18:48.632058+00:00
-- url     : https://prove2.me/theorems/aa9727e6-bbbd-4eb9-8c2a-cdf9707ae1d6
-- title:
--   Finite predictable generator tail representation
-- statement:
--   Every finite sum of predictable generators restricted to a finite positive-time horizon is a finite adapted weighted tail-box sum off time zero, with square-integrable coefficients.
-- source:
--   Kyprianou (2006), Exercise 4.4, finite-band simple kernels

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_predictableGeneratorTailBox
open MeasureTheory Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- A finite sum of marked predictable generators has a physical tail-box representation. -/
theorem Kyprianou.Ch04.finiteGeneratorSumTailRepresentation
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (t : NNReal) (B : Set ℝ) (hB : MeasurableSet B)
    (k : ℕ) (D : Fin k → Set ((NNReal × Omega) × ℝ)) (c : Fin k → ℝ)
    (hD : ∀ i, D i ∈ insert Set.univ (insert ∅
      (Set.image2 (· ×ˢ ·)
        {S : Set (NNReal × Omega) |
          (∃ A : Set Omega, MeasurableSet[F ⊥] A ∧ S = ({⊥} ×ˢ A)) ∨
          (∃ a : NNReal, ∃ A : Set Omega, MeasurableSet[F a] A ∧ S = (Set.Ioi a ×ˢ A))}
        {C : Set ℝ | MeasurableSet C}))) :
    ∃ (a : Fin k → NNReal) (C : Fin k → Set ℝ) (H : Fin k → Omega → ℝ),
      (∀ i, a i ≤ t) ∧ (∀ i, MeasurableSet (C i)) ∧ (∀ i, C i ⊆ B) ∧
      (∀ i, StronglyMeasurable[F (a i)] (H i)) ∧
      (∀ i, Integrable (fun w => (H i w)^2) P) ∧
      ∀ (w : Omega) (z : ℝ × ℝ), z.1 ≠ 0 →
        (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B).indicator
          (fun z => ∑ i, c i * (D i).indicator (fun _ => (1 : ℝ))
            ((z.1.toNNReal,w),z.2)) z =
        ∑ i, (Set.Ioc (a i : ℝ) (t : ℝ) ×ˢ C i).indicator (fun _ => H i w) z := by
  sorry
