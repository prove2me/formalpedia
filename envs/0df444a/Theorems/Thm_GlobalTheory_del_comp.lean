-- Prove2me | Theorems.Thm_GlobalTheory_del_comp
-- name    : GlobalTheory.del_comp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:44:27.819676+00:00
-- url     : https://prove2.me/theorems/70a557b3-82fa-5057-9ffd-4c9b9671f5c1
-- title:
--   Global Theory: del comp
-- statement:
--   The Global Theory construction uses the del comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L260-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L260-L267

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

theorem GlobalTheory.del_comp {u : F → G} {φ : E → F} (hu : DifferentiableAt ℝ u (φ z))
    (hφ : DifferentiableAt ℝ φ z) (v : E) :
    del (fun x => u (φ x)) z v = del u (φ z) (del φ z v) + dbar u (φ z) (dbar φ z v) := by sorry
