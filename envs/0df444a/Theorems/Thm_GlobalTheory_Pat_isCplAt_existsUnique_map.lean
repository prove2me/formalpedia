-- Prove2me | Theorems.Thm_GlobalTheory_Pat_isCplAt_existsUnique_map
-- name    : GlobalTheory.Pat.isCplAt_existsUnique_map
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:41:44.375598+00:00
-- url     : https://prove2.me/theorems/9546c9d4-24f7-4f11-87d8-8723f4cb7dfe
-- title:
--   Pat: is Cpl At exists Unique map
-- statement:
--   The Pat construction uses the is Cpl At exists Unique map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompletionUniversalLocalHom.lean#L108-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompletionUniversalLocalHom.lean#L108-L143

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
open GlobalTheory GlobalTheory.Pat
open CplMap

theorem GlobalTheory.Pat.isCplAt_existsUnique_map : ∀ (R S S' : Type) [CommRing R] [CommRing S] [IsLocalRing S]
    [CommRing S'] [IsLocalRing S'] [IsAdicComplete (maximalIdeal S') S'] (q : Ideal R) [q.IsPrime]
    (φ : R →+* S) (ψ : R →+* S'), IsCplAt q φ → (maximalIdeal S').comap ψ = q →
    ∃! θ : S →+* S', IsLocalHom θ ∧ θ.comp φ = ψ := by sorry
