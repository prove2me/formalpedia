-- Prove2me | Theorems.Thm_GlobalTheory_isoTransvection_analyticOnNhd_uncurry
-- name    : GlobalTheory.isoTransvection.analyticOnNhd_uncurry
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:01:03.894156+00:00
-- url     : https://prove2.me/theorems/a5b28b5b-8828-4e3f-a6e0-103409d8c08a
-- title:
--   iso Transvection: analytic On Nhd uncurry
-- statement:
--   The iso Transvection construction uses the analytic On Nhd uncurry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L303-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L303-L312

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

theorem GlobalTheory.isoTransvection.analyticOnNhd_uncurry [FiniteDimensional ℂ W] :
    AnalyticOnNhd ℂ (fun p : ℂ × W => isoTransvection h x hx p.1 p.2) Set.univ := by sorry
