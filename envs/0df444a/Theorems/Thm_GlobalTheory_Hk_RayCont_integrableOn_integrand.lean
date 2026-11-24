-- Prove2me | Theorems.Thm_GlobalTheory_Hk_RayCont_integrableOn_integrand
-- name    : GlobalTheory.Hk.RayCont.integrableOn_integrand
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:35:56.423607+00:00
-- url     : https://prove2.me/theorems/42fe033e-c8ae-4e7f-ac52-bbb09745772d
-- title:
--   Ray Cont: integrable On integrand
-- statement:
--   The Ray Cont construction uses the integrable On integrand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionFamilyContinuationGrowth.lean#L68-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionFamilyContinuationGrowth.lean#L68-L74

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

theorem GlobalTheory.Hk.RayCont.integrableOn_integrand (hE : Measurable E)
    (hC : ∀ x, 1 ≤ x → ‖E x‖ ≤ C * Real.sqrt x) {s : ℂ} (hs : 1 / 2 < s.re) :
    IntegrableOn (fun t : ℝ => E t * (t : ℂ) ^ (-s - 1)) (Set.Ioi (1 : ℝ)) := by sorry
