-- Prove2me | Theorems.Thm_Kyprianou_Ch04_physicalKernelDifferenceIdentityAEV1
-- name    : Kyprianou.Ch04.physicalKernelDifferenceIdentityAEV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:50:54.356795+00:00
-- url     : https://prove2.me/theorems/2866cef6-ce5e-48ab-9957-55cfb57c80ef
-- title:
--   physicalKernelDifferenceIdentityAEV1
-- statement:
--   Compensated physical integration is linear for two bounded predictable kernels on a common finite mark band, simultaneously at every time.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.physicalKernelDifferenceIdentityAEV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν] (F : Filtration NNReal inferInstance)
    (N : PoissonRandomMeasure.{0,0,0} P ν) (B : Set ℝ) (hB : MeasurableSet B)
    (hfin : ν B < ⊤)
    (g h : (NNReal × Ω) × ℝ → ℝ)
    (hg : Measurable[F.predictable.prod inferInstance] g)
    (hh : Measurable[F.predictable.prod inferInstance] h)
    (K : ℝ) (hC : ∀ p, ‖g p‖ ≤ K ∧ ‖h p‖ ≤ K)
    (hs : ∀ p, p.2 ∉ B → g p = 0 ∧ h p = 0) :
    let J := fun (k : (NNReal × Ω) × ℝ → ℝ) (t : NNReal) (w : Ω) =>
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ), k ((z.1.toNNReal,w),z.2) ∂(N.N w)) -
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ), k ((z.1.toNNReal,w),z.2) ∂referenceIntensity ν
    ∀ᵐ w ∂P, ∀ t, J (fun p => g p-h p) t w = J g t w-J h t w := by
  sorry
