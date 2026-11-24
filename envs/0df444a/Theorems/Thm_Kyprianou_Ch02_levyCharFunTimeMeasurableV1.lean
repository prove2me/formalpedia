-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyCharFunTimeMeasurableV1
-- name    : Kyprianou.Ch02.levyCharFunTimeMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:03:50.215727+00:00
-- url     : https://prove2.me/theorems/c9fa6ebf-64c5-4151-8c8a-0fadd0238a64
-- title:
--   levyCharFunTimeMeasurableV1
-- statement:
--   levyCharFunTimeMeasurableV1
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.levyCharFunTimeMeasurableV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P) (ξ : ℝ) :
    Measurable (fun r : ℝ≥0 => charFun (P.map (X r)) ξ) := by sorry
