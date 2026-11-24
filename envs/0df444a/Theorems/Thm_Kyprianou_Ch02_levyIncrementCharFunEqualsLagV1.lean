-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyIncrementCharFunEqualsLagV1
-- name    : Kyprianou.Ch02.levyIncrementCharFunEqualsLagV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:03:49.535257+00:00
-- url     : https://prove2.me/theorems/83c6f7ec-781f-4db9-9f6f-eee1efa4b7aa
-- title:
--   levyIncrementCharFunEqualsLagV1
-- statement:
--   levyIncrementCharFunEqualsLagV1
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.levyIncrementCharFunEqualsLagV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P) (s t : ℝ≥0) (hst : s ≤ t) (ξ : ℝ) :
    charFun (P.map (increment X s t)) ξ = charFun (P.map (X (t-s))) ξ := by sorry
