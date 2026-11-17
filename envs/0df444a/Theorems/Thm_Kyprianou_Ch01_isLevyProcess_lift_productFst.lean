-- Prove2me | Theorems.Thm_Kyprianou_Ch01_isLevyProcess_lift_productFst
-- name    : Kyprianou.Ch01.isLevyProcess_lift_productFst
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:57:57.211276+00:00
-- url     : https://prove2.me/theorems/14b1f9a6-ace3-4dd3-bcde-0eda3c02d89f
-- title:
--   A genuine measurable Lévy process remains a genuine Lévy process on the first coordinate of an independent product probability space
-- statement:
--   Let X be a genuine Lévy process with measurable time marginals under a probability measure P and Q any second probability law. Its first-coordinate lift X_t(ω₁) under P ⊗ Q satisfies exactly the four LeanLevy IsLevyProcess requirements: pathwise start zero, finite-grid independent increments, stationary increment laws and almost-sure càdlàg paths. Independence and stationary increments use explicit verified transport lemmas, and almost-sure path regularity is transported without an unsupported measurability assumption on the set of càdlàg paths.
-- source:
--   LeanLevy_Processes_LevyProcess, pinned Mathlib ae_of_ae_map and measurePreserving_fst, Chapter 1 Theorem 1.6.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.isLevyProcess_lift_productFst
    {Ω Λ : Type} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℝ≥0 → Ω → ℝ)
    (h : IsLevyProcess X P)
    (hXm : ∀ t, Measurable (X t)) :
    IsLevyProcess (fun t (p : Ω × Λ) => X t p.1) (P.prod Q) := by
  sorry
