-- Prove2me | Theorems.Thm_GlobalTheory_OrbitsInAffineOpens_of_locally_on_base
-- name    : GlobalTheory.OrbitsInAffineOpens.of_locally_on_base
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:15:25.182863+00:00
-- url     : https://prove2.me/theorems/fd2a8c5b-0b9c-4fe5-979d-e4820908f4b3
-- title:
--   Orbits In Affine Opens: of locally on base
-- statement:
--   The Orbits In Affine Opens construction uses the of locally on base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsInvariantSectionMemBasicOpenIff.lean#L165-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsInvariantSectionMemBasicOpenIff.lean#L165-L176

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

theorem GlobalTheory.OrbitsInAffineOpens.of_locally_on_base [Finite G] (ρ : G →* Aut X) (f : X ⟶ Y) (hf : ∀ g, (ρ g).hom ≫ f = f)
    (h : ∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧ FiniteSubsetsInAffineOpens (f ⁻¹ᵁ W)) :
    OrbitsInAffineOpens ρ := by sorry
