-- Prove2me | Theorems.Thm_GlobalTheory_leviForm_log_normSq_add_comp
-- name    : GlobalTheory.leviForm_log_normSq_add_comp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:33.235664+00:00
-- url     : https://prove2.me/theorems/8acfb8cf-09f2-4726-a671-e19d8caf4e97
-- title:
--   Global Theory: levi Form log norm Sq add comp
-- statement:
--   The Global Theory construction uses the levi Form log norm Sq add comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L676-L684
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L676-L684

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
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedSpace ℝ H]
  [IsScalarTower ℝ ℂ H]
variable {φ : E → H} {z : E}

theorem GlobalTheory.leviForm_log_normSq_add_comp {δ : ℝ} (hφ : ContDiffAt ℂ 2 φ z)
    (hz : ‖φ z‖ ^ 2 + δ ≠ 0) (v w : E) :
    leviForm (fun x => Real.log (‖φ x‖ ^ 2 + δ)) z v w =
      inner ℂ (fderiv ℂ φ z w) (fderiv ℂ φ z v) / ((‖φ z‖ ^ 2 + δ : ℝ) : ℂ)
        - inner ℂ (φ z) (fderiv ℂ φ z v) * inner ℂ (fderiv ℂ φ z w) (φ z)
          / ((‖φ z‖ ^ 2 + δ : ℝ) : ℂ) ^ 2 := by sorry
