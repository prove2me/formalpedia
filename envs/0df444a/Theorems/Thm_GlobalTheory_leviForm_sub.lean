-- Prove2me | Theorems.Thm_GlobalTheory_leviForm_sub
-- name    : GlobalTheory.leviForm_sub
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:49:04.6612+00:00
-- url     : https://prove2.me/theorems/d7b209ec-2bbe-498a-bb7c-31101fa2f7cd
-- title:
--   Global Theory: levi Form sub
-- statement:
--   The Global Theory construction uses the levi Form sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L541-L544
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L541-L544

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology ComplexConjugate
noncomputable section
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G]
  [IsScalarTower ℝ ℂ G]
variable {u u' : E → ℝ} {z : E}

theorem GlobalTheory.leviForm_sub (hu : ContDiffAt ℝ 2 u z) (hu' : ContDiffAt ℝ 2 u' z) :
    leviForm (fun x => u x - u' x) z = leviForm u z - leviForm u' z := by sorry
