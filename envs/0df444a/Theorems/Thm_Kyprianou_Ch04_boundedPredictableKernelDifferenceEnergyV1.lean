-- Prove2me | Theorems.Thm_Kyprianou_Ch04_boundedPredictableKernelDifferenceEnergyV1
-- name    : Kyprianou.Ch04.boundedPredictableKernelDifferenceEnergyV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:33:24.998261+00:00
-- url     : https://prove2.me/theorems/9c0d638d-9861-4326-9cbf-3f773777ad5b
-- title:
--   Terminal difference energy of bounded predictable kernels
-- statement:
--   Two bounded predictable kernels on a common finite band have exact
--   terminal difference energy in the positive-time intensity product.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(ii).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem boundedPredictableKernelDifferenceEnergyV1 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal inferInstance) (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (u : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Icc (0 : ℝ) (u : ℝ) ×ˢ univ → Measurable[F u] (fun ω => N.N ω D))
    (T : NNReal) (B : Set ℝ) (hB : MeasurableSet B) (hfin : ν B < ⊤)
    (g h : (NNReal × Ω) × ℝ → ℝ)
    (hg : Measurable[F.predictable.prod inferInstance] g)
    (hh : Measurable[F.predictable.prod inferInstance] h)
    (C : ℝ) (hC : ∀ p, ‖g p‖ ≤ C ∧ ‖h p‖ ≤ C)
    (hs : ∀ p, p.2 ∉ B → g p = 0 ∧ h p = 0) :
    let U := Icc (0 : ℝ) (T : ℝ) ×ˢ (univ : Set ℝ)
    let q := fun (ω : Ω) (z : ℝ × ℝ) => ((z.1.toNNReal,ω),z.2)
    let J := fun (k : (NNReal × Ω) × ℝ → ℝ) ω =>
      (∫ z in U, k (q ω z) ∂(N.N ω)) - ∫ z in U, k (q ω z) ∂referenceIntensity ν
    (∫ ω, (J g ω - J h ω)^2 ∂P) = ∫ ω, ∫ s in Ioc (0 : ℝ) (T : ℝ),
      ∫ x, (g ((s.toNNReal,ω),x) - h ((s.toNNReal,ω),x))^2 ∂ν ∂volume ∂P := by
  sorry
end Kyprianou.Ch04
