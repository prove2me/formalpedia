-- Prove2me | Theorems.Thm_Kyprianou_Ch04_boundedSupportedPredictablePhysicalCenteredV1
-- name    : Kyprianou.Ch04.boundedSupportedPredictablePhysicalCenteredV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:18:23.13207+00:00
-- url     : https://prove2.me/theorems/ce9f8093-4670-4422-8164-f0328a4dd1aa
-- title:
--   Centred bounded predictable physical compensation
-- statement:
--   Bounded marked predictable kernels of finite mark support are centred after compensation.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem boundedSupportedPredictablePhysicalCenteredV1 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal inferInstance) (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (T : NNReal) (B : Set ℝ) (hB : MeasurableSet B) (hfin : ν B < ⊤)
    (g : (NNReal × Ω) × ℝ → ℝ)
    (hg : Measurable[F.predictable.prod inferInstance] g)
    (C : ℝ) (hC : ∀ p, ‖g p‖ ≤ C) (hs : ∀ p, p.2 ∉ B → g p = 0) :
    let U := Icc (0 : ℝ) (T : ℝ) ×ˢ (univ : Set ℝ)
    let J := fun ω => (∫ z in U, g ((z.1.toNNReal,ω),z.2) ∂(N.N ω)) -
      ∫ z in U, g ((z.1.toNNReal,ω),z.2) ∂referenceIntensity ν
    Integrable J P ∧ (∫ ω, J ω ∂P) = 0 := by
  sorry
end Kyprianou.Ch04
