-- Prove2me | Theorems.Thm_GlobalTheory_exists_stable_isAffineOpen
-- name    : GlobalTheory.exists_stable_isAffineOpen
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:42:45.729945+00:00
-- url     : https://prove2.me/theorems/ad746fd7-3a91-4090-8566-151cb7685e95
-- title:
--   Global Theory: exists stable is Affine Open
-- statement:
--   The Global Theory construction uses the exists stable is Affine Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsInvariantSectionMemBasicOpenIff.lean#L296-L335
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsInvariantSectionMemBasicOpenIff.lean#L296-L335

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
variable {ρ : G →* Aut X}
variable [Finite G]
variable (ρ)

theorem GlobalTheory.exists_stable_isAffineOpen [OrbitsInAffineOpens ρ] (x : X) :
    ∃ V : X.Opens, IsAffineOpen V ∧ (∀ g, V ≤ (ρ g).hom ⁻¹ᵁ V) ∧ x ∈ V := by sorry
