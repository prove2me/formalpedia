-- Prove2me | Theorems.Thm_GlobalTheory_CompletionEmbed_algebraMap_injective
-- name    : GlobalTheory.CompletionEmbed.algebraMap_injective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:24:51.927004+00:00
-- url     : https://prove2.me/theorems/7ea1c452-d2ed-4b18-853c-075456ab8e46
-- title:
--   Completion Embed: algebra Map injective
-- statement:
--   The Completion Embed construction uses the algebra Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFinitePadicIntDomainEmbedding.lean#L32-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFinitePadicIntDomainEmbedding.lean#L32-L44

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

theorem GlobalTheory.CompletionEmbed.algebraMap_injective [IsNoetherianRing C] :
    Function.Injective (algebraMap C (AdicCompletion (maximalIdeal C) C)) := by sorry
