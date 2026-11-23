-- Prove2me | Theorems.Thm_GlobalTheory_Hk_RayCont_sum_norm_isBigO
-- name    : GlobalTheory.Hk.RayCont.sum_norm_isBigO
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:53.883238+00:00
-- url     : https://prove2.me/theorems/ab8cbd99-ea6c-401d-a3ff-34a7b8d1704f
-- title:
--   Ray Cont: sum norm is Big O
-- statement:
--   The Ray Cont construction uses the sum norm is Big O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionFamilyContinuationGrowth.lean#L125-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionFamilyContinuationGrowth.lean#L125-L144

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

theorem GlobalTheory.Hk.RayCont.sum_norm_isBigO :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖𝓕.aChi χ k‖) =O[atTop] fun n => (n : ℝ) ^ (1 : ℝ) := by sorry
