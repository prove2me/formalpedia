-- Prove2me | Theorems.Thm_GlobalTheory_CompletionEmbed_exists_pow_le_span
-- name    : GlobalTheory.CompletionEmbed.exists_pow_le_span
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:25:54.718798+00:00
-- url     : https://prove2.me/theorems/e641caec-acc1-4e41-a3df-8b1d2328d65c
-- title:
--   Completion Embed: exists pow le span
-- statement:
--   The Completion Embed construction uses the exists pow le span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFinitePadicIntDomainEmbedding.lean#L46-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFinitePadicIntDomainEmbedding.lean#L46-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiniteOfFiniteQuotMapOfIsPrecomplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNoetherianRingAdicCompletionOfNoetherian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinitePadicIntDomainEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CompletionEmbed
variable (p : ℕ) [Fact p.Prime] (C : Type) [CommRing C] [IsLocalRing C]

theorem GlobalTheory.CompletionEmbed.exists_pow_le_span [IsNoetherianRing C] (hp0 : (p : C) ≠ 0)
    (hprime : ∀ P : Ideal C, P.IsPrime → P ≠ ⊥ → P = maximalIdeal C) :
    ∃ N : ℕ, maximalIdeal C ^ N ≤ Ideal.span {(p : C)} := by sorry
