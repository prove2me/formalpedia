-- Prove2me | Theorems.Thm_GlobalTheory_IsAffineQuotient_orbitsInAffineOpens
-- name    : GlobalTheory.IsAffineQuotient.orbitsInAffineOpens
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:11:28.423129+00:00
-- url     : https://prove2.me/theorems/8ea8e076-98a8-4dd2-be03-1b6bc20ab3f6
-- title:
--   Is Affine Quotient: orbits In Affine Opens
-- statement:
--   The Is Affine Quotient construction uses the orbits In Affine Opens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsInvariantSectionMemBasicOpenIff.lean#L201-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsInvariantSectionMemBasicOpenIff.lean#L201-L204

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsInvariantSectionMemBasicOpenIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {G : Type v} [Group G] {X Y : Scheme.{u}}

theorem GlobalTheory.IsAffineQuotient.orbitsInAffineOpens {ρ : G →* Aut X} {π : X ⟶ Y}
    (h : IsAffineQuotient ρ π) : OrbitsInAffineOpens ρ := by sorry
