-- Prove2me | Theorems.Thm_GlobalTheory_Pat_CplMap_exists_val
-- name    : GlobalTheory.Pat.CplMap.exists_val
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:42:38.713416+00:00
-- url     : https://prove2.me/theorems/1b103da0-c90e-4bf7-ab91-5f7b6ff072ce
-- title:
--   Cpl Map: exists val
-- statement:
--   The Cpl Map construction uses the exists val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompletionUniversalLocalHom.lean#L44-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompletionUniversalLocalHom.lean#L44-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCplAtApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompletionUniversalLocalHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing GlobalTheory.Pat
open GlobalTheory GlobalTheory.Pat GlobalTheory.Pat.CplMap
variable {R S S' : Type} [CommRing R] [CommRing S] [IsLocalRing S] [CommRing S'] [IsLocalRing S']
  {q : Ideal R} {φ : R →+* S} {ψ : R →+* S'}
variable [hq : q.IsPrime]

theorem GlobalTheory.Pat.CplMap.exists_val (hφ : IsCplAt q φ) (hψ : (maximalIdeal S').comap ψ = q) (n : ℕ) (s : S) :
    ∃ t, IsVal q φ ψ n s t := by sorry
