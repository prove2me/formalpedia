-- Prove2me | Theorems.Thm_Kyprianou_Ch03_temperedStableProductDifferenceCharV1
-- name    : Kyprianou.Ch03.temperedStableProductDifferenceCharV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T16:51:18.887477+00:00
-- url     : https://prove2.me/theorems/595ef909-c337-4655-96d7-02b5d780cd53
-- title:
--   Characteristic function of a difference under independent product measure
-- statement:
--   Use the characteristic-function integral, change variables under the measurable maps, then factor the Fourier character of a difference and integrate over the product measure.
-- source:
--   Kyprianou (2006), Exercise 3.4; auxiliary product-difference law for temperedStableDecomposition.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.temperedStableProductDifferenceCharV1
    {OmegaP OmegaM : Type} [MeasurableSpace OmegaP] [MeasurableSpace OmegaM]
    (PP : Measure OmegaP) (PM : Measure OmegaM)
    [IsProbabilityMeasure PP] [IsProbabilityMeasure PM]
    (U : OmegaP → ℝ) (V : OmegaM → ℝ)
    (hU : Measurable U) (hV : Measurable V) (xi : ℝ) :
    charFun ((PP.prod PM).map (fun z => U z.1 - V z.2)) xi =
      charFun (PP.map U) xi * charFun (PM.map V) (-xi) := by sorry
