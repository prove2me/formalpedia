-- Prove2me | Theorems.Thm_GlobalTheory_T_completion_unique_up_to_iso
-- name    : GlobalTheory.T.completion_unique_up_to_iso
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:32:09.274893+00:00
-- url     : https://prove2.me/theorems/bf5dd471-340f-4a00-909e-cfc9c1045dee
-- title:
--   T: completion unique up to iso
-- statement:
--   The T construction uses the completion unique up to iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompletionUniqueUpToIsoStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompletionUniqueUpToIsoStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompletionUniqueUpToIso
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompletionUniqueUpToIsoStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing GlobalTheory.Pat
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.completion_unique_up_to_iso : ∀ (R S S' : Type) [CommRing R] [CommRing S] [IsLocalRing S] [CommRing S'] [IsLocalRing S'] (q : Ideal R) [q.IsPrime] (φ : R →+* S) (φ' : R →+* S'), IsCplAt q φ → IsCplAt q φ' → ∃ e : S ≃+* S', (e : S →+* S').comp φ = φ' := by sorry
