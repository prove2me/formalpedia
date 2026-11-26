-- Prove2me | Theorems.Thm_IsLowerSemianalytic_add
-- name    : IsLowerSemianalytic.add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:07:40.8968+00:00
-- url     : https://prove2.me/theorems/1b2a177c-351f-46c6-990e-5790099577a7
-- title:
--   Is Lower Semianalytic: add
-- statement:
--   The sum of two lower semianalytic functions is lower semianalytic.
--       (BS, Lemma 7.30) Proof: in `ℝ≥0∞` (with truncated subtraction),
--       `{f + g < c} = ⋃ (q : ℚ), ({f < q} ∩ {g < c - q})`, a countable union of
--       binary intersections of analytic sets.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/LsaAlgebra.lean#L22-L41
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/LsaAlgebra.lean#L22-L41

import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LsaAlgebra
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal
noncomputable section
variable {X : Type*} [TopologicalSpace X]

theorem IsLowerSemianalytic.add [T2Space X] {f g : X → ℝ≥0∞}
    (hf : IsLowerSemianalytic f) (hg : IsLowerSemianalytic g) :
    IsLowerSemianalytic (fun x => f x + g x) := by sorry
