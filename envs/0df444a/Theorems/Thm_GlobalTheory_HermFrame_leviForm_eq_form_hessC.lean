-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_leviForm_eq_form_hessC
-- name    : GlobalTheory.HermFrame.leviForm_eq_form_hessC
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:07:03.247807+00:00
-- url     : https://prove2.me/theorems/59df97fd-21be-41d9-bc33-44aad07f7c98
-- title:
--   Herm Frame: levi Form eq form hess C
-- statement:
--   The Herm Frame construction uses the levi Form eq form hess C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L615-L627
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L615-L627

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
variable {ι : Type*} [Fintype ι]

theorem GlobalTheory.HermFrame.leviForm_eq_form_hessC {D : ℕ} {u : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (hu : ContDiffAt ℝ 2 u z) (ξ η : Fin D → ℂ) :
    leviForm u z ξ η = form (ReciprocityTheory.AnForm.hessC u z) ξ η := by sorry
