-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_del_form
-- name    : GlobalTheory.HermFrame.del_form
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:06:53.976789+00:00
-- url     : https://prove2.me/theorems/7b9b97dd-45ba-527c-9d87-6f73f0d8f4d5
-- title:
--   Herm Frame: del form
-- statement:
--   The Herm Frame construction uses the del form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L365-L389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L365-L389

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m n l : Type*}
variable [Fintype n] [DecidableEq n]
variable {U : Set E} {H H' : E → Matrix n n ℂ} {z : E} {j k : WithTop ℕ∞}

theorem GlobalTheory.HermFrame.del_form (hH : MContDiffAt 1 H z) (hu : IsUnit (H z).det) {s t : E → n → ℂ}
    (hs : ∀ a, ContDiffAt ℝ 1 (fun x => s x a) z) (ht : ∀ a, ContDiffAt ℝ 1 (fun x => t x a) z)
    (ξ : E) : del (fun x => form (H x) (s x) (t x)) z ξ =
      form (H z) (covDel H s z ξ) (t z) + form (H z) (s z) fun a => dbar (fun x => t x a) z ξ := by sorry
