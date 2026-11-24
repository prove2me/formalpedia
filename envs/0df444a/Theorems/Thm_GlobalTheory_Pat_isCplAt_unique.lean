-- Prove2me | Theorems.Thm_GlobalTheory_Pat_isCplAt_unique
-- name    : GlobalTheory.Pat.isCplAt_unique
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:42:32.138086+00:00
-- url     : https://prove2.me/theorems/fa53c7e0-192f-4b57-aa51-19eba0034ae5
-- title:
--   Pat: is Cpl At unique
-- statement:
--   The Pat construction uses the is Cpl At unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompletionUniqueUpToIso.lean#L8-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompletionUniqueUpToIso.lean#L8-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompletionUniversalLocalHomStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompletionUniqueUpToIso
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

theorem GlobalTheory.Pat.isCplAt_unique : ∀ (R S S' : Type) [CommRing R] [CommRing S] [IsLocalRing S] [CommRing S'] [IsLocalRing S'] (q : Ideal R) [q.IsPrime] (φ : R →+* S) (φ' : R →+* S'), IsCplAt q φ → IsCplAt q φ' → ∃ e : S ≃+* S', (e : S →+* S').comp φ = φ' := by sorry
