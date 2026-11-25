-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_conn_comp_holo
-- name    : GlobalTheory.HermFrame.conn_comp_holo
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:07:04.73518+00:00
-- url     : https://prove2.me/theorems/f8bc0f15-345e-477c-85fd-8514b91a33fa
-- title:
--   Herm Frame: conn comp holo
-- statement:
--   The Herm Frame construction uses the conn comp holo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L546-L551
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L546-L551

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

theorem GlobalTheory.HermFrame.conn_comp_holo (h : MContDiffAt 1 H (φ w)) (hφ : DifferentiableAt ℂ φ w) (ξ : E') :
    conn (fun x => H (φ x)) w ξ = conn H (φ w) (fderiv ℂ φ w ξ) := by sorry
