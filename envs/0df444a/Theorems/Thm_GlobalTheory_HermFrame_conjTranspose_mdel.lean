-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_conjTranspose_mdel
-- name    : GlobalTheory.HermFrame.conjTranspose_mdel
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:40:24.377086+00:00
-- url     : https://prove2.me/theorems/fefd7091-40b1-4dd2-becc-974fff518ff7
-- title:
--   Herm Frame: conj Transpose mdel
-- statement:
--   The Herm Frame construction uses the conj Transpose mdel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L256-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L256-L258

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

theorem GlobalTheory.HermFrame.conjTranspose_mdel {A : E → Matrix n n ℂ} (h : ∀ᶠ x in 𝓝 z, (A x).IsHermitian) (ξ : E) :
    (mdel A z ξ)ᴴ = mdbar A z ξ := by sorry
