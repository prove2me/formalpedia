-- Prove2me | Theorems.Thm_GlobalTheory_IsAffineQuotient_exists_comp_eq_of_isAlgClosed
-- name    : GlobalTheory.IsAffineQuotient.exists_comp_eq_of_isAlgClosed
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:11:09.975967+00:00
-- url     : https://prove2.me/theorems/a34fc055-4e65-4e12-b7de-4e61933f7d0e
-- title:
--   Is Affine Quotient: exists comp eq of is Alg Closed
-- statement:
--   The Is Affine Quotient construction uses the exists comp eq of is Alg Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsDomainAndIsIntegrallyClosedLocalizationOfIsInv.lean#L862-L877
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsDomainAndIsIntegrallyClosedLocalizationOfIsInv.lean#L862-L877

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
open GlobalTheory.IsAffineQuotient
variable {G : Type v} [Group G] [Finite G] {X Y : Scheme.{u}} {ρ : G →* Aut X} {π : X ⟶ Y}
  (h : IsAffineQuotient ρ π) {k : Type u} [Field k]
include h

theorem GlobalTheory.IsAffineQuotient.exists_comp_eq_of_isAlgClosed [IsAlgClosed k] (y : Spec (.of k) ⟶ Y) :
    ∃ x : Spec (.of k) ⟶ X, x ≫ π = y := by sorry
