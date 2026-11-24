-- Prove2me | Theorems.Thm_GlobalTheory_hasSum_cosets_smaller_level_relIndex_mul
-- name    : GlobalTheory.hasSum_cosets_smaller_level_relIndex_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:50:01.226014+00:00
-- url     : https://prove2.me/theorems/ad2ccd07-c4bb-4561-b916-7a83b6ca0834
-- title:
--   Global Theory: has Sum cosets smaller level rel Index mul
-- statement:
--   The Global Theory construction uses the has Sum cosets smaller level rel Index mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumCosetsSmallerLevelRelIndexMul.lean#L28-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumCosetsSmallerLevelRelIndexMul.lean#L28-L92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumCosetsSmallerLevelRelIndexMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open QuotientGroup

theorem GlobalTheory.hasSum_cosets_smaller_level_relIndex_mul : ∀ {G : Type} [Group G] (K J H Γ : Subgroup G), K ≤ J → J ≤ H → H ≤ Γ → K.relIndex J ≠ 0 → ∀ (Ψ : G → ℂ) (z : ℂ), (∀ g ∈ Γ, g ∉ H → Ψ g = 0) → (∀ g ∈ Γ, ∀ k ∈ J, Ψ (g * k) = Ψ g) → HasSum (fun y : H ⧸ J.subgroupOf H => Ψ (y.out : H)) z → HasSum (fun y : Γ ⧸ K.subgroupOf Γ => Ψ (y.out : Γ)) ((K.relIndex J : ℂ) * z) := by sorry
