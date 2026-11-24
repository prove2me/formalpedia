-- Prove2me | Theorems.Thm_GlobalTheory_CharNormHalf_normTwist_apply
-- name    : GlobalTheory.CharNormHalf.normTwist_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:07:51.214094+00:00
-- url     : https://prove2.me/theorems/b3d0fa5c-0de9-424f-bf63-ffa54ce3c764
-- title:
--   Char Norm Half: norm Twist apply
-- statement:
--   The Char Norm Half construction uses the norm Twist apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormMulNormalisedAbsPowHalfEqOne.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormMulNormalisedAbsPowHalfEqOne.lean#L22-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntIndMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormMulNormalisedAbsPowHalfEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix ValuativeRel
noncomputable section
open GlobalTheory GlobalTheory.CharNormHalf
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.CharNormHalf.normTwist_apply (d : ℕ) (χ : kˣ →* ℂˣ) (x : kˣ) :
    (normTwist d χ x : ℂ) = ((‖(χ x : ℂ)‖ : ℝ) : ℂ) * GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2)) := by sorry
