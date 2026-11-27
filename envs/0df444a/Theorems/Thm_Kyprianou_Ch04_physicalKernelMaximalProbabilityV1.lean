-- Prove2me | Theorems.Thm_Kyprianou_Ch04_physicalKernelMaximalProbabilityV1
-- name    : Kyprianou.Ch04.physicalKernelMaximalProbabilityV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:24:47.634394+00:00
-- url     : https://prove2.me/theorems/0fc186b1-e5e6-4979-bd91-c160c23c1545
-- title:
--   physicalKernelMaximalProbabilityV1
-- statement:
--   Uniform compact outer-probability bound for a bounded physical marked predictable kernel via the terminal isometry.
-- source:
--   Kyprianou (2006), Exercise 4.5(iii)

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_boundedSupportedPredictablePhysicalMartingaleV1
import Theorems.Thm_Kyprianou_Ch04_boundedSupportedPredictablePhysicalIsometryV1
import Theorems.Thm_Kyprianou_Ch04_rightContinuousMartingaleL2MaximalV1
import Theorems.Thm_Kyprianou_Ch04_rightContinuousMartingaleCompactBddV1
import Theorems.Thm_Kyprianou_Ch04_compactSquareSupProbabilityV1
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A bounded marked predictable physical kernel inherits the compact L2
maximal probability bound from its terminal isometry. -/

theorem Kyprianou.Ch04.physicalKernelMaximalProbabilityV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (X : NNReal → Ω → ℝ) (F : Filtration NNReal inferInstance)
    (hF : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (u : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Icc (0 : ℝ) (u : ℝ) ×ˢ univ → Measurable[F u] (fun w => N.N w D))
    (B : Set ℝ) (hB : MeasurableSet B) (hfin : ν B < ⊤)
    (g : (NNReal × Ω) × ℝ → ℝ) (hg : Measurable[F.predictable.prod inferInstance] g)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ p, ‖g p‖ ≤ C)
    (hs : ∀ p, p.2 ∉ B → g p = 0)
    (T : NNReal) (hT : 0 < T) (q : ℝ)
    (hq : (∫ w, ∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ (univ : Set ℝ),
      (g ((z.1.toNNReal,w),z.2))^2 ∂referenceIntensity ν ∂P) ≤ q) :
    let J := fun (t : NNReal) w =>
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ univ, g ((z.1.toNNReal,w),z.2) ∂(N.N w)) -
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ univ, g ((z.1.toNNReal,w),z.2) ∂referenceIntensity ν
    (∀ᵐ w ∂P, ∀ t, Tendsto (fun s => J s w) (nhdsWithin t (Ioi t)) (nhds (J t w))) →
    ∀ δ : ℝ, 0 < δ →
      P {w | ∃ t ≤ T, δ < |J t w|} ≤ ENNReal.ofReal (4*q) / ENNReal.ofReal (δ^2) := by
  sorry
