-- Prove2me | Theorems.Thm_GlobalTheory_ddbar_apply_self
-- name    : GlobalTheory.ddbar_apply_self
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:14:29.770188+00:00
-- url     : https://prove2.me/theorems/c003b718-d344-466c-a320-885cd93b0d07
-- title:
--   Global Theory: ddbar apply self
-- statement:
--   The Global Theory construction uses the ddbar apply self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L394-L397
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L394-L397

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
variable {u u' : E → F} {z : E}

theorem GlobalTheory.ddbar_apply_self (hu : ContDiffAt ℝ 2 u z) (v : E) :
    ddbar u z v v = (1 / 4 : ℂ) • (fderiv ℝ (fderiv ℝ u) z v v
      + fderiv ℝ (fderiv ℝ u) z (I • v) (I • v)) := by sorry
