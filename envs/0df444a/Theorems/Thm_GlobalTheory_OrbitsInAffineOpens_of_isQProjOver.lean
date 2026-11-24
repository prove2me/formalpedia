-- Prove2me | Theorems.Thm_GlobalTheory_OrbitsInAffineOpens_of_isQProjOver
-- name    : GlobalTheory.OrbitsInAffineOpens.of_isQProjOver
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:41:50.602852+00:00
-- url     : https://prove2.me/theorems/00bb2708-113d-4b9a-9acd-1d5b3ae14329
-- title:
--   Orbits In Affine Opens: of is QProj Over
-- statement:
--   The Orbits In Affine Opens construction uses the of is QProj Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsInvariantSectionMemBasicOpenIff.lean#L159-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsInvariantSectionMemBasicOpenIff.lean#L159-L163

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
open GlobalTheory.OrbitsInAffineOpens

theorem GlobalTheory.OrbitsInAffineOpens.of_isQProjOver [Finite G] {R : Type} [CommRing R] {X : Scheme.{0}}
    {f : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R} (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver f)
    (ρ : G →* Aut X) : OrbitsInAffineOpens ρ := by sorry
