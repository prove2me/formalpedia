-- Prove2me | Theorems.Thm_GlobalTheory_FiniteSubsetsInAffineOpens_of_isProjOver
-- name    : GlobalTheory.FiniteSubsetsInAffineOpens.of_isProjOver
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:05:06.846456+00:00
-- url     : https://prove2.me/theorems/c6e04378-043a-51e0-b92c-fa5c304b4007
-- title:
--   Finite Subsets In Affine Opens: of is Proj Over
-- statement:
--   The Finite Subsets In Affine Opens construction uses the of is Proj Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsInvariantSectionMemBasicOpenIff.lean#L133-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsInvariantSectionMemBasicOpenIff.lean#L133-L137

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
variable {X Y : Scheme.{u}}
open GlobalTheory.FiniteSubsetsInAffineOpens

theorem GlobalTheory.FiniteSubsetsInAffineOpens.of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}}
    {f : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R} (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver f) :
    FiniteSubsetsInAffineOpens X := by sorry
