-- Prove2me | Theorems.Thm_GlobalTheory_OrbitsInAffineOpens_of_equivariant
-- name    : GlobalTheory.OrbitsInAffineOpens.of_equivariant
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:16:47.606559+00:00
-- url     : https://prove2.me/theorems/4213da86-0f8f-5a15-a901-1718803b2a1b
-- title:
--   Orbits In Affine Opens: of equivariant
-- statement:
--   The Orbits In Affine Opens construction uses the of equivariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsInvariantSectionMemBasicOpenIff.lean#L178-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsInvariantSectionMemBasicOpenIff.lean#L178-L184

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsInvariantSectionMemBasicOpenIff
import Theorems.Thm_GlobalTheory_IsFreeAction_of_equivariant

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

theorem GlobalTheory.OrbitsInAffineOpens.of_equivariant (ρ : G →* Aut X) (τ : G →* Aut Y) [OrbitsInAffineOpens τ] (p : X ⟶ Y)
    [IsAffineHom p] (hp : ∀ g, (ρ g).hom ≫ p = p ≫ (τ g).hom) : OrbitsInAffineOpens ρ := by sorry
