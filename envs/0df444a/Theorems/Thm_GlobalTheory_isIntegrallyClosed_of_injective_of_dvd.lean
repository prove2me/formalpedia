-- Prove2me | Theorems.Thm_GlobalTheory_isIntegrallyClosed_of_injective_of_dvd
-- name    : GlobalTheory.isIntegrallyClosed_of_injective_of_dvd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:58:44.910844+00:00
-- url     : https://prove2.me/theorems/0d999fc8-5eb8-40fa-933a-896291b7a2a2
-- title:
--   Global Theory: is Integrally Closed of injective of dvd
-- statement:
--   The Global Theory construction uses the is Integrally Closed of injective of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsDomainAndIsIntegrallyClosedLocalizationOfIsInv.lean#L34-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsDomainAndIsIntegrallyClosedLocalizationOfIsInv.lean#L34-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {A : Type*} [CommRing A] [MulSemiringAction G A]

theorem GlobalTheory.isIntegrallyClosed_of_injective_of_dvd {R S : Type*} [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [IsIntegrallyClosed S] (φ : R →+* S) (hφ : Function.Injective φ)
    (h : ∀ a b : R, b ≠ 0 → φ b ∣ φ a → b ∣ a) : IsIntegrallyClosed R := by sorry
