-- Prove2me | Theorems.Thm_MeasureTheory_Measure_map_snd_prod_of_isProbabilityMeasure
-- name    : MeasureTheory.Measure.map_snd_prod_of_isProbabilityMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:10:51.565572+00:00
-- url     : https://prove2.me/theorems/27c56bfb-7104-4da1-a7ce-6742cd45b762
-- title:
--   Measure: map snd prod of is Probability Measure
-- statement:
--   The second marginal of a product measure is the second factor, when
--       the first factor is a probability measure.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/FeasNonempty.lean#L40-L44
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/FeasNonempty.lean#L40-L44

import Definitions.Def_BicausalOT_MultiPeriod
import Definitions.Def_BicausalOT_ValueRepresentation
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_BicausalOT_FeasNonempty
set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section

theorem MeasureTheory.Measure.map_snd_prod_of_isProbabilityMeasure
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [SFinite ν] :
    (μ.prod ν).map Prod.snd = ν := by sorry
