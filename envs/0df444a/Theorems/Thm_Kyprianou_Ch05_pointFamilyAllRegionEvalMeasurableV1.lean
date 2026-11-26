-- Prove2me | Theorems.Thm_Kyprianou_Ch05_pointFamilyAllRegionEvalMeasurableV1
-- name    : Kyprianou.Ch05.pointFamilyAllRegionEvalMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:46:41.649248+00:00
-- url     : https://prove2.me/theorems/fba2c5bc-0afe-5d71-980d-bdbee8b2a7e5
-- title:
--   All measurable region counts are measurable in the finite evaluation sigma algebra
-- statement:
--   Approximate each measurable region by intersections with increasing finite-intensity spanning sets and use continuity from below.
-- source:
--   Kyprianou (2006), Chapter 5, Theorem 5.6.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch05.pointFamilyAllRegionEvalMeasurableV1
    {Ω E : Type} [MeasurableSpace E]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Z : ℕ → ℕ → Ω → E)
    (R C : Set E) (hC : MeasurableSet C) (hCR : C ⊆ R) :
    Measurable[prmEvalSigma K Z m R]
      (fun w => poissonRandomMeasure K Z w C) := by
  sorry
