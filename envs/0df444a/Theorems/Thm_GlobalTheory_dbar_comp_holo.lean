-- Prove2me | Theorems.Thm_GlobalTheory_dbar_comp_holo
-- name    : GlobalTheory.dbar_comp_holo
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:12:43.88303+00:00
-- url     : https://prove2.me/theorems/95657ec5-d1b8-4083-882e-1d6ee7e24a60
-- title:
--   Global Theory: dbar comp holo
-- statement:
--   The Global Theory construction uses the dbar comp holo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L276-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L276-L281

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
variable {f g : E → F} {z : E}

theorem GlobalTheory.dbar_comp_holo {u : F → G} {φ : E → F} (hu : DifferentiableAt ℝ u (φ z))
    (hφ : DifferentiableAt ℂ φ z) (v : E) :
    dbar (fun x => u (φ x)) z v = dbar u (φ z) (fderiv ℂ φ z v) := by sorry
