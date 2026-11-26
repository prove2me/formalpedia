-- Prove2me | Theorems.Thm_Kyprianou_Ch04_physicalRestrictedGeneratorSumIsometry
-- name    : Kyprianou.Ch04.physicalRestrictedGeneratorSumIsometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:21:27.510858+00:00
-- url     : https://prove2.me/theorems/f67cbf17-595a-43f8-97a5-3e161a23537d
-- title:
--   Physical finite-band generator-sum isometry
-- statement:
--   The compensated Poisson integral of any finite sum of marked predictable generator indicators on a finite band has the exact expected square equal to the intensity square integral.
-- source:
--   Kyprianou (2006), Exercise 4.4, finite-band simple isometry

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_physicalTailSumIsometry
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- Physical finite-band isometry for finite sums of predictable generator indicators. -/
theorem Kyprianou.Ch04.physicalRestrictedGeneratorSumIsometry
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure ℝ) [SigmaFinite nu]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P nu)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P nu F N)
    (hPast : ∀ (u : NNReal) (E : Set (ℝ × ℝ)), MeasurableSet E →
      E ⊆ Set.Icc (0 : ℝ) (u : ℝ) ×ˢ Set.univ →
      Measurable[F u] (fun w => N.N w E))
    (t : NNReal) (B : Set ℝ) (hB : MeasurableSet B) (hfin : nu B < ⊤)
    (k : ℕ) (D : Fin k → Set ((NNReal × Omega) × ℝ)) (c : Fin k → ℝ)
    (hD : ∀ i, D i ∈ insert Set.univ (insert ∅
      (Set.image2 (· ×ˢ ·)
        {S : Set (NNReal × Omega) |
          (∃ A : Set Omega, MeasurableSet[F ⊥] A ∧ S = ({⊥} ×ˢ A)) ∨
          (∃ a : NNReal, ∃ A : Set Omega, MeasurableSet[F a] A ∧ S = (Set.Ioi a ×ˢ A))}
        {C : Set ℝ | MeasurableSet C}))) :
    let U := Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B
    let K := fun w (z : ℝ × ℝ) => ∑ i, c i *
      (D i).indicator (fun _ => (1 : ℝ)) ((z.1.toNNReal,w),z.2)
    let X := fun w => (∫ z in U, K w z ∂(N.N w)) -
      ∫ z in U, K w z ∂referenceIntensity nu
    Integrable (fun w => (X w)^2) P ∧
      (∫ w, (X w)^2 ∂P) = ∫ w, ∫ z in U, (K w z)^2 ∂referenceIntensity nu ∂P := by
  sorry
