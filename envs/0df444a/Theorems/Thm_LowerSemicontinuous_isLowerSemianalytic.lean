-- Prove2me | Theorems.Thm_LowerSemicontinuous_isLowerSemianalytic
-- name    : LowerSemicontinuous.isLowerSemianalytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T07:59:38.034423+00:00
-- url     : https://prove2.me/theorems/a2f0809b-0c0c-50d1-aacf-e892a015faab
-- title:
--   Lower Semicontinuous: is Lower Semianalytic
-- statement:
--   l.s.c. functions are lower semianalytic.
--       Proof: {f < c} is open for l.s.c. f, hence Borel, hence analytic.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/LowerSemianalytic.lean#L23-L30
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/LowerSemianalytic.lean#L23-L30

import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LowerSemianalytic
set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
variable {X : Type*} [TopologicalSpace X]

theorem LowerSemicontinuous.isLowerSemianalytic
    [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {f : X → ENNReal} (hf : LowerSemicontinuous f) :
    IsLowerSemianalytic f := by sorry
