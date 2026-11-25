-- Prove2me | Theorems.Thm_GlobalTheory_T_hasSum_cosets_smaller_level_relIndex_mul_alt
-- name    : GlobalTheory.T.hasSum_cosets_smaller_level_relIndex_mul_alt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:32:47.692779+00:00
-- url     : https://prove2.me/theorems/dc23de58-bca3-4387-84d9-b457bbb6e800
-- title:
--   T: has Sum cosets smaller level rel Index mul alt
-- statement:
--   The T construction uses the has Sum cosets smaller level rel Index mul alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumCosetsSmallerLevelRelIndexMulStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumCosetsSmallerLevelRelIndexMulStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumCosetsSmallerLevelRelIndexMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumCosetsSmallerLevelRelIndexMulStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hasSum_cosets_smaller_level_relIndex_mul_alt : ∀ {G : Type} [Group G] (K J H Γ : Subgroup G), K ≤ J → J ≤ H → H ≤ Γ → K.relIndex J ≠ 0 → ∀ (Ψ : G → ℂ) (z : ℂ), (∀ g ∈ Γ, g ∉ H → Ψ g = 0) → (∀ g ∈ Γ, ∀ k ∈ J, Ψ (g * k) = Ψ g) → HasSum (fun y : H ⧸ J.subgroupOf H => Ψ (y.out : H)) z → HasSum (fun y : Γ ⧸ K.subgroupOf Γ => Ψ (y.out : Γ)) ((K.relIndex J : ℂ) * z) := by sorry
