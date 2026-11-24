-- Prove2me | Theorems.Thm_GlobalTheory_DegreeOne_surjective_of_unique_injective_localHom
-- name    : GlobalTheory.DegreeOne.surjective_of_unique_injective_localHom
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:44:48.272222+00:00
-- url     : https://prove2.me/theorems/8d58ccdd-6682-4e46-ac09-934cd3c81ff8
-- title:
--   Degree One: surjective of unique injective local Hom
-- statement:
--   The Degree One construction uses the surjective of unique injective local Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SurjectiveFiniteOfUniqueEmbeddingCompleteNormal.lean#L7-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SurjectiveFiniteOfUniqueEmbeddingCompleteNormal.lean#L7-L92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveFiniteOfUniqueEmbeddingCompleteNormal
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
open GlobalTheory GlobalTheory.DegreeOne

theorem GlobalTheory.DegreeOne.surjective_of_unique_injective_localHom : ∀ (B R : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [IsIntegrallyClosed B] [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (ψ : B →+* R), IsAdicComplete (maximalIdeal B) B → Function.Injective ψ → ψ.Finite → (∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [CharZero R'], IsAdicComplete (maximalIdeal R') R' → ∀ f g : R →+* R', Function.Injective f → Function.Injective g → IsLocalHom f → IsLocalHom g → f.comp ψ = g.comp ψ → f = g) → Function.Surjective ψ := by sorry
