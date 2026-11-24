-- Prove2me | Theorems.Thm_GlobalTheory_Hk_RayCont_norm_rem_le
-- name    : GlobalTheory.Hk.RayCont.norm_rem_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:00:50.231939+00:00
-- url     : https://prove2.me/theorems/f3011d4b-765e-4f1d-82d5-d4d8becb060c
-- title:
--   Ray Cont: norm rem le
-- statement:
--   The Ray Cont construction uses the norm rem le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionFamilyContinuationGrowth.lean#L95-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionFamilyContinuationGrowth.lean#L95-L112

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RayCont
open Asymptotics
variable (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ)

theorem GlobalTheory.Hk.RayCont.norm_rem_le (x : ℝ) (hx : 1 ≤ x) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, 𝓕.aChi χ n) - 𝓕.res χ * x‖ ≤ 10 * 𝓕.B * Real.sqrt x := by sorry
