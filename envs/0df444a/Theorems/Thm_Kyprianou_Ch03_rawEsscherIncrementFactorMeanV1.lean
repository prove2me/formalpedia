-- Prove2me | Theorems.Thm_Kyprianou_Ch03_rawEsscherIncrementFactorMeanV1
-- name    : Kyprianou.Ch03.rawEsscherIncrementFactorMeanV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T23:00:32.356334+00:00
-- url     : https://prove2.me/theorems/851a4a9f-42ec-4ec7-ae3d-a3fb3cd8612d
-- title:
--   Normalised Esscher increment factor has unit extended mean
-- statement:
--   Stationarity identifies the increment distribution with the process at the elapsed time. The normalised density at that time has unit mean.
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

theorem Kyprianou.Ch03.rawEsscherIncrementFactorMeanV1
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (beta : ℝ) (hm : ∀ t, Measurable (X t)) (k : ℝ)
    (hunit : ∀ t : NNReal, Integrable (esscherDensity X beta k t) P ∧
      (∫ w, esscherDensity X beta k t w ∂P) = 1)
    (s t : NNReal) (hst : s ≤ t) :
    (∫⁻ w, ENNReal.ofReal (Real.exp (beta * (X t w - X s w) -
      k * ((t - s : NNReal) : ℝ))) ∂P) = 1 := by
  sorry
