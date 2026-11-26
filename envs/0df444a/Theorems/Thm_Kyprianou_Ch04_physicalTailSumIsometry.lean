-- Prove2me | Theorems.Thm_Kyprianou_Ch04_physicalTailSumIsometry
-- name    : Kyprianou.Ch04.physicalTailSumIsometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:13:45.516417+00:00
-- url     : https://prove2.me/theorems/b536fc48-4baf-503a-b454-4d26c5e4f4af
-- title:
--   physicalTailSumIsometry
-- statement:
--   A physical kernel equal to a finite predictable tail sum outside time zero inherits its Poisson isometry.
-- source:
--   Kyprianou (2006), Exercise 4.4, physical finite predictable approximation.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_finitePredictableTailBoxPhysicalIsometry
import Theorems.Thm_Kyprianou_Ch04_poissonCountZeroOfReferenceZero
import Theorems.Thm_Kyprianou_Ch04_referenceIntensityTimeBoxFinite
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- Isometry for a kernel equal to a finite predictable tail sum off time zero. -/
theorem Kyprianou.Ch04.physicalTailSumIsometry
    {Omega ι : Type} [MeasurableSpace Omega] [DecidableEq ι]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure ℝ) [SigmaFinite nu]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P nu)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P nu F N)
    (hPast : ∀ (u : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Set.Icc (0 : ℝ) (u : ℝ) ×ˢ Set.univ →
      Measurable[F u] (fun w => N.N w D))
    (s : Finset ι) (t : NNReal) (a : ι → NNReal)
    (B : ι → Set ℝ) (H : ι → Omega → ℝ)
    (hat : ∀ i ∈ s, a i ≤ t)
    (hB : ∀ i ∈ s, MeasurableSet (B i))
    (hFin : ∀ i ∈ s, nu (B i) ≠ ⊤)
    (hH : ∀ i ∈ s, StronglyMeasurable[F (a i)] (H i))
    (hH2 : ∀ i ∈ s, Integrable (fun w => (H i w)^2) P)
    (K : Omega → (ℝ × ℝ) → ℝ)
    (hK : ∀ w z, z.1 ≠ 0 →
      K w z = ∑ i ∈ s, (Set.Ioc (a i : ℝ) (t : ℝ) ×ˢ B i).indicator
        (fun _ => H i w) z) :
    let X := fun w => (∫ z, K w z ∂(N.N w)) - ∫ z, K w z ∂referenceIntensity nu
    Integrable (fun w => (X w)^2) P ∧
      (∫ w, (X w)^2 ∂P) = ∫ w, ∫ z, (K w z)^2 ∂referenceIntensity nu ∂P := by
  sorry
