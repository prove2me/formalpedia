-- Prove2me | Theorems.Thm_Kyprianou_Ch04_fullClockSupportedBandSquare
-- name    : Kyprianou.Ch04.fullClockSupportedBandSquare
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:42:22.043369+00:00
-- url     : https://prove2.me/theorems/298f17c3-3a93-5b61-82af-4723ebbcf49a
-- title:
--   Full clock finite-support square identity
-- statement:
--   The full physical compensated Poisson integral satisfies the exact square identity for every predictable kernel supported on a finite mark band, using the full expected clock measure.
-- source:
--   Kyprianou (2006), Exercise 4.4

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The full physical square identity for a predictable kernel supported on a finite mark band. -/
theorem Kyprianou.Ch04.fullClockSupportedBandSquare
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure ℝ) [SigmaFinite nu]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P nu)
    (hFuture : IsFutureIndependentPoissonMeasure P nu F N)
    (hPast : ∀ (u : NNReal) (E : Set (ℝ × ℝ)), MeasurableSet E →
      E ⊆ Set.Icc (0 : ℝ) (u : ℝ) ×ˢ Set.univ →
      Measurable[F u] (fun w => N.N w E))
    (t : NNReal) (B : Set ℝ) (hB : MeasurableSet B) (hfin : nu B < ⊤)
    [mAll : MeasurableSpace ((NNReal × Omega) × ℝ)]
    (hAll : mAll = F.predictable.prod (inferInstance : MeasurableSpace ℝ))
    (mu : Measure ((NNReal × Omega) × ℝ))
    (hClock : ∀ f : ((NNReal × Omega) × ℝ) → ENNReal, Measurable f →
      AEMeasurable (fun w => ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
        f ((z.1.toNNReal,w),z.2) ∂referenceIntensity nu) P ∧
      (∫⁻ p, f p ∂mu) = (∫⁻ w, ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
        f ((z.1.toNNReal,w),z.2) ∂referenceIntensity nu ∂P))
    (g : ((NNReal × Omega) × ℝ) → ℝ) (hgm : Measurable g) (hg : MemLp g 2 mu)
    (hsupp : ∀ a, a.2 ∉ B → g a = 0) :
    let V := Set.Icc (0 : ℝ) (t : ℝ) ×ˢ (Set.univ : Set ℝ)
    let X := fun w => (∫ z in V, g ((z.1.toNNReal,w),z.2) ∂(N.N w)) -
      ∫ z in V, g ((z.1.toNNReal,w),z.2) ∂referenceIntensity nu
    Integrable (fun w => (X w)^2) P ∧ (∫ w, (X w)^2 ∂P) = ∫ a, (g a)^2 ∂mu := by
  sorry
