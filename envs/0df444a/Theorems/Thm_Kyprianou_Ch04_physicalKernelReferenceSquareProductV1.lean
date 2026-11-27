-- Prove2me | Theorems.Thm_Kyprianou_Ch04_physicalKernelReferenceSquareProductV1
-- name    : Kyprianou.Ch04.physicalKernelReferenceSquareProductV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:50:44.663902+00:00
-- url     : https://prove2.me/theorems/c38211da-38cd-5762-bee9-1db00a23a5c1
-- title:
--   physicalKernelReferenceSquareProductV1
-- statement:
--   The physical reference-intensity square integral equals its iterated positive-time and mark integral.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.physicalKernelReferenceSquareProductV1 {Ω : Type} [MeasurableSpace Ω]
    (ν : Measure ℝ) [SigmaFinite ν] (F : Filtration NNReal inferInstance)
    (B : Set ℝ) (hB : MeasurableSet B) (hfin : ν B < ⊤)
    (g : (NNReal × Ω) × ℝ → ℝ)
    (hg : Measurable[F.predictable.prod inferInstance] g)
    (C : ℝ) (hC : ∀ p, ‖g p‖ ≤ C) (hs : ∀ p, p.2 ∉ B → g p = 0)
    (T : NNReal) (w : Ω) :
    (∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ (univ : Set ℝ),
      (g ((z.1.toNNReal,w),z.2))^2 ∂referenceIntensity ν) =
    ∫ s in Ioc (0 : ℝ) (T : ℝ), ∫ x, (g ((s.toNNReal,w),x))^2 ∂ν ∂volume := by
  sorry
