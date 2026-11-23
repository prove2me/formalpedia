-- Prove2me | Theorems.Thm_GlobalTheory_ddbar_comp_holo
-- name    : GlobalTheory.ddbar_comp_holo
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:12:53.163142+00:00
-- url     : https://prove2.me/theorems/34aae32a-ff65-47dc-b795-186a1e72810a
-- title:
--   Global Theory: ddbar comp holo
-- statement:
--   The Global Theory construction uses the ddbar comp holo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L450-L479
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L450-L479

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

theorem GlobalTheory.ddbar_comp_holo {u : F → G} {φ : E → F} (hu : ContDiffAt ℝ 2 u (φ z))
    (hφ : ContDiffAt ℂ 2 φ z) (v w : E) :
    ddbar (fun x => u (φ x)) z v w = ddbar u (φ z) (fderiv ℂ φ z v) (fderiv ℂ φ z w) := by sorry
