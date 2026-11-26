-- Prove2me | Theorems.Thm_Kyprianou_Ch04_boundedSupportedPredictablePhysicalMartingaleV1
-- name    : Kyprianou.Ch04.boundedSupportedPredictablePhysicalMartingaleV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:45:04.533511+00:00
-- url     : https://prove2.me/theorems/de5a3030-bd54-443a-8790-f2891e71b7b9
-- title:
--   Bounded supported predictable physical compensation martingale
-- statement:
--   Prove the compensated finite-band physical integral is a martingale in the completed natural filtration by measurable past evaluations, finite-intensity integrability and conditional centring on arbitrary past events.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem boundedSupportedPredictablePhysicalMartingaleV1 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (X : NNReal → Ω → ℝ) (F : Filtration NNReal inferInstance)
    (hF : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (u : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Icc (0 : ℝ) (u : ℝ) ×ˢ univ → Measurable[F u] (fun w => N.N w D))
    (B : Set ℝ) (hB : MeasurableSet B) (hfin : ν B < ⊤)
    (g : (NNReal × Ω) × ℝ → ℝ)
    (hg : Measurable[F.predictable.prod inferInstance] g)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ p, ‖g p‖ ≤ C)
    (hs : ∀ p, p.2 ∉ B → g p = 0) :
    let J := fun (t : NNReal) w =>
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ univ, g ((z.1.toNNReal,w),z.2) ∂(N.N w)) -
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ univ, g ((z.1.toNNReal,w),z.2) ∂referenceIntensity ν
    Martingale J F P := by
  sorry
end Kyprianou.Ch04
