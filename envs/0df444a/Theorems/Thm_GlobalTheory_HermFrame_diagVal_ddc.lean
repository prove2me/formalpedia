-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_diagVal_ddc
-- name    : GlobalTheory.HermFrame.diagVal_ddc
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:07:47.870062+00:00
-- url     : https://prove2.me/theorems/69177c90-35b6-444a-8457-9e54b5fb620a
-- title:
--   Herm Frame: diag Val ddc
-- statement:
--   The Herm Frame construction uses the diag Val ddc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L607-L613
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L607-L613

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

theorem GlobalTheory.HermFrame.diagVal_ddc {u : (ι → ℂ) → ℝ} {z : ι → ℂ} (hu : ContDiffAt ℝ 2 u z) (ξ : ι → ℂ) :
    diagVal (ddc u z) ξ = ReciprocityTheory.AnForm.levi u z ξ / (2 * Real.pi) := by sorry
