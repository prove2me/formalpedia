-- Prove2me | Theorems.Thm_GlobalTheory_del_sum
-- name    : GlobalTheory.del_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:12:26.607747+00:00
-- url     : https://prove2.me/theorems/b6884b6f-2ec4-45d6-9c5a-31543e04c88c
-- title:
--   Global Theory: del sum
-- statement:
--   The Global Theory construction uses the del sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L202-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L202-L205

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

theorem GlobalTheory.del_sum {ι : Type*} {t : Finset ι} {A : ι → E → F}
    (h : ∀ i ∈ t, DifferentiableAt ℝ (A i) z) :
    del (fun x => ∑ i ∈ t, A i x) z = ∑ i ∈ t, del (A i) z := by sorry
