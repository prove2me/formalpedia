-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WeilCoinv_exists_dotProduct_ne_one
-- name    : GlobalTheory.CompanionTheory.WeilCoinv.exists_dotProduct_ne_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:21:24.754258+00:00
-- url     : https://prove2.me/theorems/b2624e8f-6ea0-44b5-8081-4f2ebf251d64
-- title:
--   Weil Coinv: exists dot Product ne one
-- statement:
--   The Weil Coinv construction uses the exists dot Product ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/ExistsEqMulApplyZero.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/ExistsEqMulApplyZero.lean#L10-L19

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

theorem GlobalTheory.CompanionTheory.WeilCoinv.exists_dotProduct_ne_one {k : Type} [Field k] {κ : Type} [Fintype κ] {ψ : AddChar k ℂ} (hψ : ψ ≠ 1)
    {x : κ → k} (hx : x ≠ 0) : ∃ y : κ → k, ψ (x ⬝ᵥ y) ≠ 1 := by sorry
