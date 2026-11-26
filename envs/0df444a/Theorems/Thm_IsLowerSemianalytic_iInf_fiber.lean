-- Prove2me | Theorems.Thm_IsLowerSemianalytic_iInf_fiber
-- name    : IsLowerSemianalytic.iInf_fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T07:59:37.324965+00:00
-- url     : https://prove2.me/theorems/a711d878-6aa8-5d5c-892d-f6e05a4be18f
-- title:
--   Is Lower Semianalytic: i Inf fiber
-- statement:
--   inf of lower semianalytic is lower semianalytic. (BS, Prop 7.47)
--       Proof: {x | inf < c} = projₓ({(x,y) ∈ D | f(x,y) < c}).
--       Intersection of two analytic sets is analytic; projection preserves analytic.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/LowerSemianalytic.lean#L35-L61
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/LowerSemianalytic.lean#L35-L61

import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LowerSemianalytic
set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
variable {X : Type*} [TopologicalSpace X]

theorem IsLowerSemianalytic.iInf_fiber
    {Y : Type*} [TopologicalSpace Y] [PolishSpace X] [PolishSpace Y]
    [T2Space X]
    {D : Set (X × Y)} (hD : AnalyticSet D)
    {f : X × Y → ENNReal} (hf : IsLowerSemianalytic (X := X × Y) f) :
    IsLowerSemianalytic (fun x => ⨅ (y : Y) (_ : (x, y) ∈ D), f (x, y)) := by sorry
