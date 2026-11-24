-- Prove2me | Theorems.Thm_GlobalTheory_exists_apply_eq_apply_smul
-- name    : GlobalTheory.exists_apply_eq_apply_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:30:20.349779+00:00
-- url     : https://prove2.me/theorems/f692f5a4-8638-48af-95f1-1597eff843d2
-- title:
--   Global Theory: exists apply eq apply smul
-- statement:
--   The Global Theory construction uses the exists apply eq apply smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsDomainAndIsIntegrallyClosedLocalizationOfIsInv.lean#L198-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsDomainAndIsIntegrallyClosedLocalizationOfIsInv.lean#L198-L209

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

theorem GlobalTheory.exists_apply_eq_apply_smul (φ ψ : A →+* k)
    (h : ∀ a, (∀ g : G, g • a = a) → φ a = ψ a) (a : A) : ∃ g : G, ψ a = φ (g • a) := by sorry
