-- Prove2me | Theorems.Thm_Kyprianou_Ch04_boundedSupportedPredictablePhysicalIsometryV1
-- name    : Kyprianou.Ch04.boundedSupportedPredictablePhysicalIsometryV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:24:51.465285+00:00
-- url     : https://prove2.me/theorems/60ca1faa-1e27-44e2-9980-ab896f1deac9
-- title:
--   Physical isometry for bounded finite-band predictable kernels
-- statement:
--   The physical isometry for a bounded predictable kernel supported on a finite mark band.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem boundedSupportedPredictablePhysicalIsometryV1 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (u : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Icc (0 : ℝ) (u : ℝ) ×ˢ univ →
      Measurable[F u] (fun ω => N.N ω D))
    (t : NNReal) (B : Set ℝ) (hB : MeasurableSet B) (hfin : ν B < ⊤)
    (g : ((NNReal × Ω) × ℝ) → ℝ)
    (hg : Measurable[F.predictable.prod inferInstance] g)
    (C : ℝ) (hC : ∀ p, ‖g p‖ ≤ C)
    (hsupp : ∀ p, p.2 ∉ B → g p = 0) :
    let U := Icc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ)
    let K := fun ω (z : ℝ × ℝ) => g ((z.1.toNNReal,ω),z.2)
    let J := fun ω => (∫ z in U, K ω z ∂(N.N ω)) -
      ∫ z in U, K ω z ∂referenceIntensity ν
    Integrable (fun ω => (J ω)^2) P ∧
      (∫ ω, (J ω)^2 ∂P) = ∫ ω, ∫ z in U, (K ω z)^2 ∂referenceIntensity ν ∂P := by
  sorry
end Kyprianou.Ch04
