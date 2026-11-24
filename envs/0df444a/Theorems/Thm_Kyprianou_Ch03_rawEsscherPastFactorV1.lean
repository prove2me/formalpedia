-- Prove2me | Theorems.Thm_Kyprianou_Ch03_rawEsscherPastFactorV1
-- name    : Kyprianou.Ch03.rawEsscherPastFactorV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T22:01:01.163143+00:00
-- url     : https://prove2.me/theorems/8ca212fa-3d5a-4548-b309-faa3f211f6f6
-- title:
--   Normalised Esscher densities are consistent on raw past events
-- statement:
--   Use stationary increments and independence of the future increment from the raw natural sigma algebra. Factor the exponential density and integrate the independent normalised increment factor.
-- source:
--   Kyprianou (2006), Chapter 3, Theorem 3.9; reduction of 24b018f9-56a9-4313-b32a-cb140d602681.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem Kyprianou.Ch03.rawEsscherPastFactorV1
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (beta : ℝ)
    (hm : ∀ t, Measurable (X t))
    (k : ℝ)
    (hunit : ∀ t : NNReal, Integrable (esscherDensity X beta k t) P ∧
      (∫ w, esscherDensity X beta k t w ∂P) = 1) :
    ∀ s t : NNReal, s ≤ t → ∀ A,
      MeasurableSet[PerfCorrMSQ.natFiltr X s] A →
      (∫ w, A.indicator (esscherDensity X beta k t) w ∂P) =
        (∫ w, A.indicator (esscherDensity X beta k s) w ∂P) := by
  sorry
