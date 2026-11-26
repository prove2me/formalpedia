-- Prove2me | Theorems.Thm_GlobalTheory_isoTransvection_differentiable_param
-- name    : GlobalTheory.isoTransvection.differentiable_param
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:47:57.130927+00:00
-- url     : https://prove2.me/theorems/4902af07-bb60-524b-aa6a-e3332fd62d40
-- title:
--   iso Transvection: differentiable param
-- statement:
--   The iso Transvection construction uses the differentiable param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L299-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L299-L301

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

theorem GlobalTheory.isoTransvection.differentiable_param (v : W) :
    Differentiable ℂ fun b : ℂ => isoTransvection h x hx b v := by sorry
