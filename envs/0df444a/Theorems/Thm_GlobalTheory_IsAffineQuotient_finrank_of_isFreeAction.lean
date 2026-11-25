-- Prove2me | Theorems.Thm_GlobalTheory_IsAffineQuotient_finrank_of_isFreeAction
-- name    : GlobalTheory.IsAffineQuotient.finrank_of_isFreeAction
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:11:33.58679+00:00
-- url     : https://prove2.me/theorems/840e156e-246e-520a-bc40-e4e46052749e
-- title:
--   Is Affine Quotient: finrank of is Free Action
-- statement:
--   The Is Affine Quotient construction uses the finrank of is Free Action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsDomainAndIsIntegrallyClosedLocalizationOfIsInv.lean#L665-L680
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsDomainAndIsIntegrallyClosedLocalizationOfIsInv.lean#L665-L680

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
variable {G : Type v} [Group G] {X Y : Scheme.{u}}
open GlobalTheory.IsAffineQuotient
variable [Finite G] {ρ : G →* Aut X} {π : X ⟶ Y} (h : IsAffineQuotient ρ π) (hρ : IsFreeAction ρ)
include h hρ

theorem GlobalTheory.IsAffineQuotient.finrank_of_isFreeAction (y : Y) : π.finrank y = Nat.card G := by sorry
