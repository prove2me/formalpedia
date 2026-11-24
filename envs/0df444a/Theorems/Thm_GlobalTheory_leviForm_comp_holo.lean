-- Prove2me | Theorems.Thm_GlobalTheory_leviForm_comp_holo
-- name    : GlobalTheory.leviForm_comp_holo
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:06:58.281287+00:00
-- url     : https://prove2.me/theorems/c1da7c07-097d-44f8-a4cb-4b66aafd0aa3
-- title:
--   Global Theory: levi Form comp holo
-- statement:
--   The Global Theory construction uses the levi Form comp holo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L565-L568
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L565-L568

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

theorem GlobalTheory.leviForm_comp_holo {u : F → ℝ} {φ : E → F} (hu : ContDiffAt ℝ 2 u (φ z))
    (hφ : ContDiffAt ℂ 2 φ z) (v w : E) :
    leviForm (fun x => u (φ x)) z v w = leviForm u (φ z) (fderiv ℂ φ z v) (fderiv ℂ φ z w) := by sorry
