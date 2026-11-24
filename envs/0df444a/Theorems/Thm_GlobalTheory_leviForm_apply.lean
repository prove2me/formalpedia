-- Prove2me | Theorems.Thm_GlobalTheory_leviForm_apply
-- name    : GlobalTheory.leviForm_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:07:02.37957+00:00
-- url     : https://prove2.me/theorems/b5cc9016-4411-4651-b4a0-8a1d1f0d173d
-- title:
--   Global Theory: levi Form apply
-- statement:
--   The Global Theory construction uses the levi Form apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L509-L514
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L509-L514

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

theorem GlobalTheory.leviForm_apply (hu : ContDiffAt ℝ 2 u z) (v w : E) :
    leviForm u z v w = (1 / 4 : ℂ) * (fderiv ℝ (fderiv ℝ u) z v w
      + fderiv ℝ (fderiv ℝ u) z (I • v) (I • w) + I * fderiv ℝ (fderiv ℝ u) z v (I • w)
      - I * fderiv ℝ (fderiv ℝ u) z (I • v) w) := by sorry
