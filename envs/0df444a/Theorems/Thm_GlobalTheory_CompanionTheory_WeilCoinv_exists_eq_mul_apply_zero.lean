-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WeilCoinv_exists_eq_mul_apply_zero
-- name    : GlobalTheory.CompanionTheory.WeilCoinv.exists_eq_mul_apply_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:01:45.301544+00:00
-- url     : https://prove2.me/theorems/11adb4c1-8a3c-4a2d-8571-37b70439ed26
-- title:
--   Weil Coinv: exists eq mul apply zero
-- statement:
--   The Weil Coinv construction uses the exists eq mul apply zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/ExistsEqMulApplyZero.lean#L21-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/ExistsEqMulApplyZero.lean#L21-L139

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsEqMulApplyZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilCoinv

theorem GlobalTheory.CompanionTheory.WeilCoinv.exists_eq_mul_apply_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (κ : Type) [Fintype κ] (ψ : AddChar k ℂ),
    Continuous ψ → ψ ≠ 1 → ∀ l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ,
    (∀ y, ∀ φ ∈ SB (κ → k), l (schr ψ (0, y) φ) = l φ) → ∃ a : ℂ, ∀ φ ∈ SB (κ → k), l φ = a * φ 0 := by sorry
