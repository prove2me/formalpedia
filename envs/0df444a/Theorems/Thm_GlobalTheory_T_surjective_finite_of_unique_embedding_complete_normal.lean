-- Prove2me | Theorems.Thm_GlobalTheory_T_surjective_finite_of_unique_embedding_complete_normal
-- name    : GlobalTheory.T.surjective_finite_of_unique_embedding_complete_normal
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:40:40.175054+00:00
-- url     : https://prove2.me/theorems/a316e793-6898-5f4d-bb03-1246c9b04118
-- title:
--   T: surjective finite of unique embedding complete normal
-- statement:
--   The T construction uses the surjective finite of unique embedding complete normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SurjectiveFiniteOfUniqueEmbeddingCompleteNormalStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SurjectiveFiniteOfUniqueEmbeddingCompleteNormalStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveFiniteOfUniqueEmbeddingCompleteNormal
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveFiniteOfUniqueEmbeddingCompleteNormalStatement
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.surjective_finite_of_unique_embedding_complete_normal : ∀ (B R : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [IsIntegrallyClosed B] [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (ψ : B →+* R), IsAdicComplete (maximalIdeal B) B → Function.Injective ψ → ψ.Finite → (∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [CharZero R'], IsAdicComplete (maximalIdeal R') R' → ∀ f g : R →+* R', Function.Injective f → Function.Injective g → IsLocalHom f → IsLocalHom g → f.comp ψ = g.comp ψ → f = g) → Function.Surjective ψ := by sorry
