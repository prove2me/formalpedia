-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_dvr_extension_of_essentially_etale_local
-- name    : GlobalTheory.T.exists_dvr_extension_of_essentially_etale_local
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:29:09.820896+00:00
-- url     : https://prove2.me/theorems/e865c171-e3b3-4eb2-8e9a-ca9d74370092
-- title:
--   T: exists dvr extension of essentially etale local
-- statement:
--   The T construction uses the exists dvr extension of essentially etale local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDvrExtensionOfEssentiallyEtaleLocalStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDvrExtensionOfEssentiallyEtaleLocalStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDvrExtensionOfEssentiallyEtaleLocal
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDvrExtensionOfEssentiallyEtaleLocalStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_dvr_extension_of_essentially_etale_local : ∀ {K K' R S : Type} [Field K] [Field K'] [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [IsLocalRing R] [IsLocalRing S] [Algebra R K] [Algebra S K'] [IsFractionRing R K] [IsFractionRing S K'] (φ : K →+* K') (σ : R →+* S) [IsLocalHom σ], σ.Flat → σ.FormallyEtale → σ.EssFiniteType → φ.comp (algebraMap R K) = (algebraMap S K').comp σ → ∀ V : ValuationSubring K, IsDiscreteValuationRing V → (∀ a, algebraMap R K a ∈ V) → ∃ (V' : ValuationSubring K') (h : ∀ x ∈ V, φ x ∈ V'), IsDiscreteValuationRing V' ∧ (∀ b, algebraMap S K' b ∈ V') ∧ (∀ x, φ x ∈ V' → x ∈ V) ∧ (φ.restrict V V' h).FormallyEtale ∧ (φ.restrict V V' h).EssFiniteType := by sorry
