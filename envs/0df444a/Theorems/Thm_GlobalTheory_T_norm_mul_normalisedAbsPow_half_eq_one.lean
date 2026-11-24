-- Prove2me | Theorems.Thm_GlobalTheory_T_norm_mul_normalisedAbsPow_half_eq_one
-- name    : GlobalTheory.T.norm_mul_normalisedAbsPow_half_eq_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:53:51.94413+00:00
-- url     : https://prove2.me/theorems/cc1524e8-a0f8-4f4b-9e5f-2b7e8aa677f3
-- title:
--   T: norm mul normalised Abs Pow half eq one
-- statement:
--   The T construction uses the norm mul normalised Abs Pow half eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormMulNormalisedAbsPowHalfEqOneStatement.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormMulNormalisedAbsPowHalfEqOneStatement.lean#L9-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormMulNormalisedAbsPowHalfEqOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntIndMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormMulNormalisedAbsPowHalfEqOneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix ValuativeRel
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.norm_mul_normalisedAbsPow_half_eq_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (χ : kˣ →* ℂˣ), (∀ u : kˣ, valuation k (u : k) = 1 → ‖(χ u : ℂ)‖ = 1) →
    ∀ ϖ : kˣ, GlobalTheory.SplitFlip.IsUnif ϖ → ‖(χ ϖ : ℂ)‖ ^ 2 * (GlobalTheory.SplitWeil.resCard k : ℝ) ^ d = 1 →
    ∀ x : kˣ, ‖(χ x : ℂ) * GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2))‖ = 1 := by sorry
