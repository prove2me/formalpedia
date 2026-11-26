-- Prove2me | Theorems.Thm_IsLowerSemianalytic_comp_continuous
-- name    : IsLowerSemianalytic.comp_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:07:44.848797+00:00
-- url     : https://prove2.me/theorems/65b85ef9-2555-433c-bf2f-7a3ced9fc0c8
-- title:
--   Is Lower Semianalytic: comp continuous
-- statement:
--   Precomposition with a continuous map preserves lower semianalyticity:
--       sublevel sets pull back to preimages of analytic sets, which are analytic
--       by `MeasureTheory.AnalyticSet.preimage_of_continuous`.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/LsaAlgebra.lean#L62-L70
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/LsaAlgebra.lean#L62-L70

import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LsaAlgebra
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal
noncomputable section
variable {X : Type*} [TopologicalSpace X]

theorem IsLowerSemianalytic.comp_continuous [PolishSpace X]
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f : Y → ℝ≥0∞} (hf : IsLowerSemianalytic f)
    {g : X → Y} (hg : Continuous g) :
    IsLowerSemianalytic (f ∘ g) := by sorry
