-- Prove2me | Theorems.Thm_GlobalTheory_CharNormHalf_norm_mul_apow_eq_one
-- name    : GlobalTheory.CharNormHalf.norm_mul_apow_eq_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:08:19.230089+00:00
-- url     : https://prove2.me/theorems/b32fb190-22e8-495d-9ebb-73a3fa03f796
-- title:
--   Char Norm Half: norm mul apow eq one
-- statement:
--   The Char Norm Half construction uses the norm mul apow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormMulNormalisedAbsPowHalfEqOne.lean#L25-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormMulNormalisedAbsPowHalfEqOne.lean#L25-L59

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

theorem GlobalTheory.CharNormHalf.norm_mul_apow_eq_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (χ : kˣ →* ℂˣ), (∀ u : kˣ, valuation k (u : k) = 1 → ‖(χ u : ℂ)‖ = 1) →
    ∀ ϖ : kˣ, GlobalTheory.SplitFlip.IsUnif ϖ → ‖(χ ϖ : ℂ)‖ ^ 2 * (GlobalTheory.SplitWeil.resCard k : ℝ) ^ d = 1 →
    ∀ x : kˣ, ‖(χ x : ℂ) * GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2))‖ = 1 := by sorry
