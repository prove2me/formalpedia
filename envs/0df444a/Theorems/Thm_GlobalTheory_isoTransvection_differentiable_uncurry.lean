-- Prove2me | Theorems.Thm_GlobalTheory_isoTransvection_differentiable_uncurry
-- name    : GlobalTheory.isoTransvection.differentiable_uncurry
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:48:05.160833+00:00
-- url     : https://prove2.me/theorems/92142594-0ef6-575f-a67f-8a48253ea716
-- title:
--   iso Transvection: differentiable uncurry
-- statement:
--   The iso Transvection construction uses the differentiable uncurry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L314-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L314-L316

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module
open GlobalTheory.isoTransvection
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] (h : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (x : W)
  (hx : h x x = 0)

theorem GlobalTheory.isoTransvection.differentiable_uncurry [FiniteDimensional ℂ W] :
    Differentiable ℂ fun p : ℂ × W => isoTransvection h x hx p.1 p.2 := by sorry
