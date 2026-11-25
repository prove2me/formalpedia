-- Prove2me | Theorems.Thm_GlobalTheory_leviForm_sum
-- name    : GlobalTheory.leviForm_sum
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:49:07.241578+00:00
-- url     : https://prove2.me/theorems/5fc133e9-5888-4747-92e8-cf58782516a0
-- title:
--   Global Theory: levi Form sum
-- statement:
--   The Global Theory construction uses the levi Form sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L559-L563
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L559-L563

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

theorem GlobalTheory.leviForm_sum {ι : Type*} {t : Finset ι} {A : ι → E → ℝ}
    (h : ∀ i ∈ t, ContDiffAt ℝ 2 (A i) z) :
    leviForm (fun x => ∑ i ∈ t, A i x) z = ∑ i ∈ t, leviForm (A i) z := by sorry
