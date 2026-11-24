-- Prove2me | Theorems.Thm_GlobalTheory_bijective_of_image_range_eq
-- name    : GlobalTheory.bijective_of_image_range_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:06:43.700487+00:00
-- url     : https://prove2.me/theorems/0cdc92a9-19b4-4f14-9f75-ee8e7422e40c
-- title:
--   Global Theory: bijective of image range eq
-- statement:
--   The Global Theory construction uses the bijective of image range eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsEqCexpQuadraticOfEquivalentFactors.lean#L117-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsEqCexpQuadraticOfEquivalentFactors.lean#L117-L125

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsEqCexpQuadraticOfEquivalentFactors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex
open GlobalTheory
variable {L L' : Type*} [AddCommGroup L] [AddCommGroup L']

theorem GlobalTheory.bijective_of_image_range_eq {V V' : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
    [Module ℝ V'] [IsScalarTower ℝ ℂ V'] (hdim : Module.finrank ℂ V = Module.finrank ℂ V')
    (h : V →ₗ[ℂ] V') {S : Set V'} (hS : Submodule.span ℝ S = ⊤) (hh : S ⊆ range h) :
    Function.Bijective h := by sorry
