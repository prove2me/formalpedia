-- Prove2me | Theorems.Thm_GlobalTheory_exists_ringHom_extension_of_isIntegral
-- name    : GlobalTheory.exists_ringHom_extension_of_isIntegral
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:40:51.217696+00:00
-- url     : https://prove2.me/theorems/29ff6a4f-a790-46c2-b6fe-3c00936e994c
-- title:
--   Global Theory: exists ring Hom extension of is Integral
-- statement:
--   The Global Theory construction uses the exists ring Hom extension of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsDomainAndIsIntegrallyClosedLocalizationOfIsInv.lean#L231-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsDomainAndIsIntegrallyClosedLocalizationOfIsInv.lean#L231-L253

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
variable {G : Type*} [Group G] [Finite G] {A k : Type*} [CommRing A] [MulSemiringAction G A]
  [CommRing k] [IsDomain k]

theorem GlobalTheory.exists_ringHom_extension_of_isIntegral {B A k : Type*} [CommRing B] [CommRing A] [Field k]
    [IsAlgClosed k] [Algebra B A] [FaithfulSMul B A] [Algebra.IsIntegral B A] (φ : B →+* k) :
    ∃ ψ : A →+* k, ψ.comp (algebraMap B A) = φ := by sorry
