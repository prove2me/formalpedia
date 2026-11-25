-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_curv_comp_holo
-- name    : GlobalTheory.HermFrame.curv_comp_holo
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:07:00.370634+00:00
-- url     : https://prove2.me/theorems/57eb3c33-5a50-424c-8f00-6bfa73cf8d83
-- title:
--   Herm Frame: curv comp holo
-- statement:
--   The Herm Frame construction uses the curv comp holo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L553-L567
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L553-L567

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
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedSpace ℝ E']
  [IsScalarTower ℝ ℂ E'] {φ : E' → E} {w : E'}

theorem GlobalTheory.HermFrame.curv_comp_holo (h : MContDiffAt 2 H (φ w)) (hu : IsUnit (H (φ w)).det)
    (hφ : ContDiffAt ℂ 2 φ w) (ξ η : E') :
    curv (fun x => H (φ x)) w ξ η = curv H (φ w) (fderiv ℂ φ w ξ) (fderiv ℂ φ w η) := by sorry
