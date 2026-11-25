-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_lineCurv_smul
-- name    : GlobalTheory.HermFrame.lineCurv_smul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:07:11.774677+00:00
-- url     : https://prove2.me/theorems/1bddf186-4980-5503-9abc-4708ff602e53
-- title:
--   Herm Frame: line Curv smul
-- statement:
--   The Herm Frame construction uses the line Curv smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L702-L707
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L702-L707

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

theorem GlobalTheory.HermFrame.lineCurv_smul (H : E → Matrix n n ℂ) (z : E) (w : n → ℂ) {c : ℂ} (hc : c ≠ 0) :
    lineCurv H z (c • w) = lineCurv H z w := by sorry
