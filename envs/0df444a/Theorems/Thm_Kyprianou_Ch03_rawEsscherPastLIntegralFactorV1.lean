-- Prove2me | Theorems.Thm_Kyprianou_Ch03_rawEsscherPastLIntegralFactorV1
-- name    : Kyprianou.Ch03.rawEsscherPastLIntegralFactorV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T23:00:25.216102+00:00
-- url     : https://prove2.me/theorems/f87dcffc-ddfe-4e8a-ad64-50e7be6bf039
-- title:
--   Normalised Esscher densities have consistent extended integrals on raw events
-- statement:
--   Factor the density into its past value and a normalised independent increment. Use independence of the raw past and future increment to factor the extended integral.
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

theorem Kyprianou.Ch03.rawEsscherPastLIntegralFactorV1
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (beta : ℝ) (hm : ∀ t, Measurable (X t)) (k : ℝ)
    (hunit : ∀ t : NNReal, Integrable (esscherDensity X beta k t) P ∧
      (∫ w, esscherDensity X beta k t w ∂P) = 1) :
    ∀ s t : NNReal, s ≤ t → ∀ A,
      MeasurableSet[PerfCorrMSQ.natFiltr X s] A →
      (∫⁻ w, A.indicator (fun w => ENNReal.ofReal (esscherDensity X beta k t w)) w ∂P) =
        (∫⁻ w, A.indicator (fun w => ENNReal.ofReal (esscherDensity X beta k s w)) w ∂P) := by
  sorry
