-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_conjTranspose_mddbar
-- name    : GlobalTheory.HermFrame.conjTranspose_mddbar
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:37:28.619184+00:00
-- url     : https://prove2.me/theorems/0fc7f1a4-6520-49cc-a7d0-ea224ad86c84
-- title:
--   Herm Frame: conj Transpose mddbar
-- statement:
--   The Herm Frame construction uses the conj Transpose mddbar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L260-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L260-L265

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
variable {A B : E → Matrix m n ℂ} {z : E} {j k : WithTop ℕ∞}

theorem GlobalTheory.HermFrame.conjTranspose_mddbar {A : E → Matrix n n ℂ} (h2 : MContDiffAt 2 A z)
    (h : ∀ᶠ x in 𝓝 z, (A x).IsHermitian) (ξ η : E) : (mddbar A z ξ η)ᴴ = mddbar A z η ξ := by sorry
