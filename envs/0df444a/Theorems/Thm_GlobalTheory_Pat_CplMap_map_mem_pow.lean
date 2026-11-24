-- Prove2me | Theorems.Thm_GlobalTheory_Pat_CplMap_map_mem_pow
-- name    : GlobalTheory.Pat.CplMap.map_mem_pow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:42:03.261803+00:00
-- url     : https://prove2.me/theorems/3810f8b0-43dd-44e9-9bd9-9da8c8bceefa
-- title:
--   Cpl Map: map mem pow
-- statement:
--   The Cpl Map construction uses the map mem pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompletionUniversalLocalHom.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompletionUniversalLocalHom.lean#L19-L24

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

theorem GlobalTheory.Pat.CplMap.map_mem_pow (hψ : (maximalIdeal S').comap ψ = q) (n : ℕ) {a : R} (ha : a ∈ q ^ n) :
    ψ a ∈ maximalIdeal S' ^ n := by sorry
