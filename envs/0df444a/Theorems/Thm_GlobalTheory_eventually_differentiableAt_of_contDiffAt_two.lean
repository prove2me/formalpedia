-- Prove2me | Theorems.Thm_GlobalTheory_eventually_differentiableAt_of_contDiffAt_two
-- name    : GlobalTheory.eventually_differentiableAt_of_contDiffAt_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:53:48.126294+00:00
-- url     : https://prove2.me/theorems/a844db1b-600a-4605-9822-d72e3df784e5
-- title:
--   Global Theory: eventually differentiable At of cont Diff At two
-- statement:
--   The Global Theory construction uses the eventually differentiable At of cont Diff At two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L321-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L321-L324

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

theorem GlobalTheory.eventually_differentiableAt_of_contDiffAt_two {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (hu : ContDiffAt 𝕜 2 u z) :
    ∀ᶠ x in 𝓝 z, DifferentiableAt 𝕜 u x := by sorry
