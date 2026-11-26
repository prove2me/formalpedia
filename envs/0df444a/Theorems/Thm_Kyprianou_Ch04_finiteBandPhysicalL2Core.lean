-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteBandPhysicalL2Core
-- name    : Kyprianou.Ch04.finiteBandPhysicalL2Core
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:30:44.021505+00:00
-- url     : https://prove2.me/theorems/750d4b2a-0675-4c30-9b7a-422c7919462e
-- title:
--   Finite marked predictable physical L2 isometry
-- statement:
--   The physical compensated Poisson integral over a finite mark band has the L2 isometry for a square-integrable predictable kernel, with respect to its expected clock measure.
-- source:
--   Kyprianou (2006), Exercise 4.4

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- Physical Poisson isometry on a finite marked predictable clock measure. -/
theorem Kyprianou.Ch04.finiteBandPhysicalL2Core
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
    [mAll : MeasurableSpace ((NNReal × Omega) × ℝ)]
    (hAll : mAll = F.predictable.prod (inferInstance : MeasurableSpace ℝ))
    (mu : Measure ((NNReal × Omega) × ℝ)) [IsFiniteMeasure mu]
    (hClock : ∀ f : ((NNReal × Omega) × ℝ) → ENNReal, Measurable f →
      AEMeasurable (fun w => ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B,
        f ((z.1.toNNReal,w),z.2) ∂(N.N w)) P ∧
      AEMeasurable (fun w => ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B,
        f ((z.1.toNNReal,w),z.2) ∂referenceIntensity nu) P ∧
      (∫⁻ p, f p ∂mu) = (∫⁻ w, ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B,
        f ((z.1.toNNReal,w),z.2) ∂(N.N w) ∂P) ∧
      (∫⁻ p, f p ∂mu) = (∫⁻ w, ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B,
        f ((z.1.toNNReal,w),z.2) ∂referenceIntensity nu ∂P))
    (g : ((NNReal × Omega) × ℝ) → ℝ) (hgm : Measurable g) (hg : MemLp g 2 mu) :
    let U := Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B
    let K := fun w (z : ℝ × ℝ) => g ((z.1.toNNReal,w),z.2)
    let X := fun w => (∫ z in U, K w z ∂(N.N w)) -
      ∫ z in U, K w z ∂referenceIntensity nu
    Integrable (fun w => (X w)^2) P ∧
      (∫ w, (X w)^2 ∂P) = ∫ w, ∫ z in U, (K w z)^2 ∂referenceIntensity nu ∂P := by
  sorry
