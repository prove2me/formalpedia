-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_curvMinor_self
-- name    : GlobalTheory.HermFrame.curvMinor_self
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:07:13.088473+00:00
-- url     : https://prove2.me/theorems/ece88d20-e59d-4737-8839-25fead8a7fef
-- title:
--   Herm Frame: curv Minor self
-- statement:
--   The Herm Frame construction uses the curv Minor self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L713-L714
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L713-L714

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

theorem GlobalTheory.HermFrame.curvMinor_self (H : E → Matrix n n ℂ) (z : E) (a : n) (ξ₁ η₁ ξ₂ η₂ : E) :
    curvMinor H z a a ξ₁ η₁ ξ₂ η₂ = 0 := by sorry
