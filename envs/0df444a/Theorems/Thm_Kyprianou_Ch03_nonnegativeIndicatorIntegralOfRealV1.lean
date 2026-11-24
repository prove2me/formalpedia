-- Prove2me | Theorems.Thm_Kyprianou_Ch03_nonnegativeIndicatorIntegralOfRealV1
-- name    : Kyprianou.Ch03.nonnegativeIndicatorIntegralOfRealV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T23:00:44.576562+00:00
-- url     : https://prove2.me/theorems/88691459-b6bb-4287-a9ac-82875ab10cf1
-- title:
--   Extended integral of a nonnegative indicator equals the embedded real integral
-- statement:
--   Apply the real-to-extended integral conversion to the integrable nonnegative indicator and commute the embedding with the indicator.
-- source:
--   Kyprianou (2006), Chapter 3, Theorem 3.9; reduction of rawEsscherPastFactorV1.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem Kyprianou.Ch03.nonnegativeIndicatorIntegralOfRealV1
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (A : Set Ω)
    (hA : MeasurableSet A) (hi : Integrable f P) (hn : ∀ w, 0 ≤ f w) :
    ENNReal.ofReal (∫ w, A.indicator f w ∂P) =
      ∫⁻ w, A.indicator (fun w => ENNReal.ofReal (f w)) w ∂P := by
  sorry
