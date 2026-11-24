-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_leviForm_self_eq_levi
-- name    : GlobalTheory.HermFrame.leviForm_self_eq_levi
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:38:24.360574+00:00
-- url     : https://prove2.me/theorems/02ef0a2f-5635-4f60-8757-efc3314fecfb
-- title:
--   Herm Frame: levi Form self eq levi
-- statement:
--   The Herm Frame construction uses the levi Form self eq levi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L603-L605
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L603-L605

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

theorem GlobalTheory.HermFrame.leviForm_self_eq_levi {u : (ι → ℂ) → ℝ} {z : ι → ℂ} (hu : ContDiffAt ℝ 2 u z)
    (ξ : ι → ℂ) : leviForm u z ξ ξ = ReciprocityTheory.AnForm.levi u z ξ := by sorry
