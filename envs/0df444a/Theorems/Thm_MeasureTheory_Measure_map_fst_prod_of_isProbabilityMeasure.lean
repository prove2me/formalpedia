-- Prove2me | Theorems.Thm_MeasureTheory_Measure_map_fst_prod_of_isProbabilityMeasure
-- name    : MeasureTheory.Measure.map_fst_prod_of_isProbabilityMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:11:09.267271+00:00
-- url     : https://prove2.me/theorems/8711f5dd-6c41-4999-a932-ab372fbba73f
-- title:
--   Measure: map fst prod of is Probability Measure
-- statement:
--   The first marginal of a product measure is the first factor, when the
--       second factor is a probability measure.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/FeasNonempty.lean#L32-L36
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/FeasNonempty.lean#L32-L36

import Definitions.Def_BicausalOT_MultiPeriod
import Definitions.Def_BicausalOT_ValueRepresentation
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_BicausalOT_FeasNonempty
set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section

theorem MeasureTheory.Measure.map_fst_prod_of_isProbabilityMeasure
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure ν] :
    (μ.prod ν).map Prod.fst = μ := by sorry
