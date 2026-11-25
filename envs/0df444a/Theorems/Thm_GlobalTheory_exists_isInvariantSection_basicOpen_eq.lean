-- Prove2me | Theorems.Thm_GlobalTheory_exists_isInvariantSection_basicOpen_eq
-- name    : GlobalTheory.exists_isInvariantSection_basicOpen_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:50:11.853421+00:00
-- url     : https://prove2.me/theorems/e611aef0-9381-5520-9c36-d476608896a5
-- title:
--   Global Theory: exists is Invariant Section basic Open eq
-- statement:
--   The Global Theory construction uses the exists is Invariant Section basic Open eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsInvariantSectionMemBasicOpenIff.lean#L274-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsInvariantSectionMemBasicOpenIff.lean#L274-L281

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

theorem GlobalTheory.exists_isInvariantSection_basicOpen_eq {U : X.Opens} (hU : ∀ g, U ≤ (ρ g).hom ⁻¹ᵁ U)
    (s : Γ(X, U)) (hs : ∀ g, X.basicOpen s ≤ (ρ g).hom ⁻¹ᵁ X.basicOpen s) :
    ∃ t : Γ(X, U), IsInvariantSection ρ U t ∧ X.basicOpen t = X.basicOpen s := by sorry
