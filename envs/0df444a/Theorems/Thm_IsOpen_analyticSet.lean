-- Prove2me | Theorems.Thm_IsOpen_analyticSet
-- name    : IsOpen.analyticSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:00:35.703852+00:00
-- url     : https://prove2.me/theorems/72868ac3-d748-4b15-81bb-d208e0d0e1e4
-- title:
--   Is Open: analytic Set
-- statement:
--   Open sets in Polish spaces are analytic.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/AnalyticSigmaAlgebra.lean#L41-L44
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/AnalyticSigmaAlgebra.lean#L41-L44

import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
variable {X : Type*} [TopologicalSpace X]

theorem IsOpen.analyticSet [PolishSpace X] {s : Set X} (hs : IsOpen s) :
    AnalyticSet s := by sorry
