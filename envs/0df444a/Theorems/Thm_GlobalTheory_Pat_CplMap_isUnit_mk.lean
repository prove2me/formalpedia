-- Prove2me | Theorems.Thm_GlobalTheory_Pat_CplMap_isUnit_mk
-- name    : GlobalTheory.Pat.CplMap.isUnit_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:05.534149+00:00
-- url     : https://prove2.me/theorems/6d7190a1-b4a0-401f-80ff-d1f30a6ca8be
-- title:
--   Cpl Map: is Unit mk
-- statement:
--   The Cpl Map construction uses the is Unit mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompletionUniversalLocalHom.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompletionUniversalLocalHom.lean#L12-L17

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

theorem GlobalTheory.Pat.CplMap.isUnit_mk (hψ : (maximalIdeal S').comap ψ = q) (n : ℕ) {b : R} (hb : b ∉ q) :
    IsUnit (Ideal.Quotient.mk (maximalIdeal S' ^ n) (ψ b)) := by sorry
