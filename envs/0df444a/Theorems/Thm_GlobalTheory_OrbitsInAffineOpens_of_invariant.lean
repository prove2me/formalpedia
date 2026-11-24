-- Prove2me | Theorems.Thm_GlobalTheory_OrbitsInAffineOpens_of_invariant
-- name    : GlobalTheory.OrbitsInAffineOpens.of_invariant
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:43:23.0728+00:00
-- url     : https://prove2.me/theorems/88a80d7c-ae70-4c3f-9df3-7a1fb4863c2a
-- title:
--   Orbits In Affine Opens: of invariant
-- statement:
--   The Orbits In Affine Opens construction uses the of invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsInvariantSectionMemBasicOpenIff.lean#L186-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsInvariantSectionMemBasicOpenIff.lean#L186-L192

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

theorem GlobalTheory.OrbitsInAffineOpens.of_invariant (ρ : G →* Aut X) (p : X ⟶ Y) [IsAffineHom p]
    (hp : ∀ g, (ρ g).hom ≫ p = p) : OrbitsInAffineOpens ρ := by sorry
