-- Prove2me | Theorems.Thm_GlobalTheory_IsAffineQuotient_comp_eq_comp_iff
-- name    : GlobalTheory.IsAffineQuotient.comp_eq_comp_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:10:49.340079+00:00
-- url     : https://prove2.me/theorems/4b5a2d9c-7199-43f6-9c22-e812cd96064b
-- title:
--   Is Affine Quotient: comp eq comp iff
-- statement:
--   The Is Affine Quotient construction uses the comp eq comp iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsDomainAndIsIntegrallyClosedLocalizationOfIsInv.lean#L837-L860
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsDomainAndIsIntegrallyClosedLocalizationOfIsInv.lean#L837-L860

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

theorem GlobalTheory.IsAffineQuotient.comp_eq_comp_iff (x y : Spec (.of k) ⟶ X) :
    x ≫ π = y ≫ π ↔ ∃ g, x ≫ (ρ g).hom = y := by sorry
