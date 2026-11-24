-- Prove2me | Theorems.Thm_GlobalTheory_Hk_RayCont_differentiableAt_integral
-- name    : GlobalTheory.Hk.RayCont.differentiableAt_integral
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:35:12.728846+00:00
-- url     : https://prove2.me/theorems/861f396b-a4af-4e08-8a23-4481628bf026
-- title:
--   Ray Cont: differentiable At integral
-- statement:
--   The Ray Cont construction uses the differentiable At integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionFamilyContinuationGrowth.lean#L33-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionFamilyContinuationGrowth.lean#L33-L53

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
variable {E : ℝ → ℂ} {C : ℝ}

theorem GlobalTheory.Hk.RayCont.differentiableAt_integral (hE : Measurable E)
    (hC : ∀ x, 1 ≤ x → ‖E x‖ ≤ C * Real.sqrt x) {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => ∫ t in Set.Ioi (1 : ℝ), E t * (t : ℂ) ^ (-z - 1)) s := by sorry
