-- Prove2me | Theorems.Thm_GlobalTheory_IsPshC2On_add
-- name    : GlobalTheory.IsPshC2On.add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:09:36.698233+00:00
-- url     : https://prove2.me/theorems/ba5d1a03-a6cb-4317-8c87-11b0f8e34f3b
-- title:
--   Is Psh C2 On: add
-- statement:
--   The Is Psh C2 On construction uses the add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L719-L723
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L719-L723

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
variable {u u' : E → ℝ} {s t : Set E}

theorem GlobalTheory.IsPshC2On.add (h : IsPshC2On u s) (h' : IsPshC2On u' s) :
    IsPshC2On (fun x => u x + u' x) s := by sorry
