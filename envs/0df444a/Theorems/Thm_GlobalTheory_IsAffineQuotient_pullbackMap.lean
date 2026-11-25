-- Prove2me | Theorems.Thm_GlobalTheory_IsAffineQuotient_pullbackMap
-- name    : GlobalTheory.IsAffineQuotient.pullbackMap
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:11:53.050907+00:00
-- url     : https://prove2.me/theorems/2d6a268b-3340-5fc4-9e70-dadd8d6ee55b
-- title:
--   Is Affine Quotient: pullback Map
-- statement:
--   The Is Affine Quotient construction uses the pullback Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsDomainAndIsIntegrallyClosedLocalizationOfIsInv.lean#L809-L812
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsDomainAndIsIntegrallyClosedLocalizationOfIsInv.lean#L809-L812

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor


set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {G : Type v} [Group G] {X Y X' Y' S S' : Scheme.{u}}
attribute [local simp] pullback.map pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc
variable (ρ : G →* Aut X) (f : X ⟶ S) (hf : ∀ g, (ρ g).hom ≫ f = f) (t : S' ⟶ S)
variable {ρ f} [Finite G] {π : X ⟶ Y} (h : IsAffineQuotient ρ π) (q : Y ⟶ S) (hq : π ≫ q = f)
include h

theorem GlobalTheory.IsAffineQuotient.pullbackMap [Flat t] : IsAffineQuotient (pullbackAction ρ f hf t)
    (pullback.map f t q t π (𝟙 _) (𝟙 _) (by simp [hq]) (by simp)) := by sorry
