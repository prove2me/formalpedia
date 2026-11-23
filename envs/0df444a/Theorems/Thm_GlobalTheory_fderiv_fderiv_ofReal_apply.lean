-- Prove2me | Theorems.Thm_GlobalTheory_fderiv_fderiv_ofReal_apply
-- name    : GlobalTheory.fderiv_fderiv_ofReal_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:12:54.158815+00:00
-- url     : https://prove2.me/theorems/2ed81a4b-dcd0-4187-b7a4-a3ed1bef8c27
-- title:
--   Global Theory: fderiv fderiv of Real apply
-- statement:
--   The Global Theory construction uses the fderiv fderiv of Real apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L496-L507
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L496-L507

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

theorem GlobalTheory.fderiv_fderiv_ofReal_apply (hu : ContDiffAt ℝ 2 u z) (v w : E) :
    fderiv ℝ (fderiv ℝ fun x => (u x : ℂ)) z v w = (fderiv ℝ (fderiv ℝ u) z v w : ℂ) := by sorry
