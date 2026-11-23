-- Prove2me | Theorems.Thm_GlobalTheory_Pat_CplMap_val_unique_of_pair
-- name    : GlobalTheory.Pat.CplMap.val_unique_of_pair
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:59:23.497516+00:00
-- url     : https://prove2.me/theorems/41348098-1144-4400-8c45-f6c2a3745b63
-- title:
--   Cpl Map: val unique of pair
-- statement:
--   The Cpl Map construction uses the val unique of pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompletionUniversalLocalHom.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompletionUniversalLocalHom.lean#L61-L66

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
omit hq

theorem GlobalTheory.Pat.CplMap.val_unique_of_pair (hψ : (maximalIdeal S').comap ψ = q) {n : ℕ} {s : S}
    {t t' : S' ⧸ maximalIdeal S' ^ n} (ht : IsVal q φ ψ n s t) {a b : R} (hb : b ∉ q)
    (h : φ b * s - φ a ∈ maximalIdeal S ^ n)
    (e : Ideal.Quotient.mk (maximalIdeal S' ^ n) (ψ b) * t' =
      Ideal.Quotient.mk (maximalIdeal S' ^ n) (ψ a)) : t = t' := by sorry
