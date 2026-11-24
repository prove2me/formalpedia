-- Prove2me | Theorems.Thm_GlobalTheory_ddbar_sum
-- name    : GlobalTheory.ddbar_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:15:20.864677+00:00
-- url     : https://prove2.me/theorems/deae2794-afdc-4442-81ef-4f1e456b3f1a
-- title:
--   Global Theory: ddbar sum
-- statement:
--   The Global Theory construction uses the ddbar sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L429-L437
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L429-L437

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

theorem GlobalTheory.ddbar_sum {ι : Type*} {t : Finset ι} {A : ι → E → F}
    (h : ∀ i ∈ t, ContDiffAt ℝ 2 (A i) z) :
    ddbar (fun x => ∑ i ∈ t, A i x) z = ∑ i ∈ t, ddbar (A i) z := by sorry
