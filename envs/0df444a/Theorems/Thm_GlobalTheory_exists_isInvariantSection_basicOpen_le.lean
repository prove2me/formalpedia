-- Prove2me | Theorems.Thm_GlobalTheory_exists_isInvariantSection_basicOpen_le
-- name    : GlobalTheory.exists_isInvariantSection_basicOpen_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:33:07.701119+00:00
-- url     : https://prove2.me/theorems/c2f433ba-c905-4a31-bd62-d8ea0d100284
-- title:
--   Global Theory: exists is Invariant Section basic Open le
-- statement:
--   The Global Theory construction uses the exists is Invariant Section basic Open le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsInvariantSectionMemBasicOpenIff.lean#L283-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsInvariantSectionMemBasicOpenIff.lean#L283-L292

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

theorem GlobalTheory.exists_isInvariantSection_basicOpen_le {U : X.Opens} (hU : IsAffineOpen U)
    (hst : ∀ g, U ≤ (ρ g).hom ⁻¹ᵁ U) {x : X} (hx : x ∈ U) (O : X.Opens)
    (hO : ∀ g, (ρ g).hom x ∈ O) :
    ∃ t : Γ(X, U), IsInvariantSection ρ U t ∧ x ∈ X.basicOpen t ∧ X.basicOpen t ≤ O := by sorry
