-- Prove2me | Theorems.Thm_GlobalTheory_IsPshC2On_mono
-- name    : GlobalTheory.IsPshC2On.mono
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:45.301963+00:00
-- url     : https://prove2.me/theorems/18a9f9e0-9c12-453a-9405-1215f979fdac
-- title:
--   Is Psh C2 On: mono
-- statement:
--   The Is Psh C2 On construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L710-L711
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L710-L711

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

theorem GlobalTheory.IsPshC2On.mono (h : IsPshC2On u t) (hst : s ⊆ t) : IsPshC2On u s := by sorry
