-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_TwoFormBound_mono
-- name    : GlobalTheory.HermFrame.TwoFormBound.mono
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:37:58.243448+00:00
-- url     : https://prove2.me/theorems/8d8cd90f-d4c7-46d0-9958-0b09d3fe255a
-- title:
--   Two Form Bound: mono
-- statement:
--   The Two Form Bound construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L648-L652
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L648-L652

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_IsPshC2On_mono

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
variable [Fintype n]
variable {U : Set (ι → ℂ)} {H : (ι → ℂ) → Matrix n n ℂ} {G : (ι → ℂ) → Matrix ι ι ℂ} {C C' : ℝ}

theorem GlobalTheory.HermFrame.TwoFormBound.mono {F : (ι → ℂ) → (ι → ℂ) → (ι → ℂ) → Matrix n n ℂ}
    (h : TwoFormBound U H G F C) (hC : C ≤ C') : TwoFormBound U H G F C' := by sorry
