-- Prove2me | Theorems.Thm_IsLowerSemianalytic_const
-- name    : IsLowerSemianalytic.const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:07:56.14164+00:00
-- url     : https://prove2.me/theorems/e9e33e17-e95e-4f52-9387-997005bdded9
-- title:
--   Is Lower Semianalytic: const
-- statement:
--   Constant functions are lower semianalytic: every strict sublevel set is
--       `univ` or `∅`.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/LsaAlgebra.lean#L45-L57
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/LsaAlgebra.lean#L45-L57

import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LsaAlgebra
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal
noncomputable section
variable {X : Type*} [TopologicalSpace X]

theorem IsLowerSemianalytic.const [PolishSpace X] (c : ℝ≥0∞) :
    IsLowerSemianalytic (fun _ : X => c) := by sorry
