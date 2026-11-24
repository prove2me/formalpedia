-- Prove2me | Theorems.Thm_GlobalTheory_Pat_flat_quotientMap_map
-- name    : GlobalTheory.Pat.flat_quotientMap_map
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:41:26.014397+00:00
-- url     : https://prove2.me/theorems/75dc15ff-c75a-49d0-a3fe-87eff3de33f8
-- title:
--   Pat: flat quotient Map map
-- statement:
--   The Pat construction uses the flat quotient Map map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSurjectiveOfIsCplAt.lean#L9-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSurjectiveOfIsCplAt.lean#L9-L30

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

theorem GlobalTheory.Pat.flat_quotientMap_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.Flat)
    (I : Ideal R) : (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map).Flat := by sorry
