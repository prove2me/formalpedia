-- Prove2me | Theorems.Thm_GlobalTheory_Pat_exists_surjective_of_isCplAt
-- name    : GlobalTheory.Pat.exists_surjective_of_isCplAt
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:17:28.779694+00:00
-- url     : https://prove2.me/theorems/d8a68350-ebdf-4703-9e40-6bca0d10fc05
-- title:
--   Pat: exists surjective of is Cpl At
-- statement:
--   The Pat construction uses the exists surjective of is Cpl At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSurjectiveOfIsCplAt.lean#L32-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSurjectiveOfIsCplAt.lean#L32-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompletionUniqueUpToIsoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSurjectiveOfIsCplAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing GlobalTheory.Pat
open GlobalTheory GlobalTheory.Pat

theorem GlobalTheory.Pat.exists_surjective_of_isCplAt : ∀ (R R' S S' : Type) [CommRing R] [IsNoetherianRing R] [CommRing R'] [CommRing S] [IsLocalRing S] [CommRing S'] [IsLocalRing S'] (π : R →+* R') (q' : Ideal R') [q'.IsPrime] (φ : R →+* S) (φ' : R' →+* S'), Function.Surjective π → IsCplAt (q'.comap π) φ → IsCplAt q' φ' → ∃ θ : S →+* S', IsLocalHom θ ∧ θ.comp φ = φ'.comp π ∧ Function.Surjective θ ∧ RingHom.ker θ = (RingHom.ker π).map φ := by sorry
