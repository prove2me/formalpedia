-- Prove2me | Theorems.Thm_Kyprianou_Ch03_rawEsscherUnitFromMomentsV1
-- name    : Kyprianou.Ch03.rawEsscherUnitFromMomentsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T22:00:53.331217+00:00
-- url     : https://prove2.me/theorems/58a0a83d-4f56-4324-8efb-e7522cd75520
-- title:
--   Normalised Esscher densities have unit mean
-- statement:
--   Use the proved log-moment time scaling and positivity of exponential moments, then multiply by the deterministic normalising exponential.
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

theorem Kyprianou.Ch03.rawEsscherUnitFromMomentsV1
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (beta : ℝ)
    (hi : ∀ t, Integrable (fun w => Real.exp (beta * X t w)) P) :
    let k := Real.log (∫ w, Real.exp (beta * X 1 w) ∂P)
    ∀ t : NNReal, Integrable (esscherDensity X beta k t) P ∧
      (∫ w, esscherDensity X beta k t w ∂P) = 1 := by
  sorry
