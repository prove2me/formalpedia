-- Prove2me | Theorems.Thm_GlobalTheory_exists_isInvariantSection_mem_basicOpen_iff
-- name    : GlobalTheory.exists_isInvariantSection_mem_basicOpen_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:42:54.415005+00:00
-- url     : https://prove2.me/theorems/b9450d56-c8ce-4b20-a041-87dbf12c9637
-- title:
--   Global Theory: exists is Invariant Section mem basic Open iff
-- statement:
--   The Global Theory construction uses the exists is Invariant Section mem basic Open iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsInvariantSectionMemBasicOpenIff.lean#L243-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsInvariantSectionMemBasicOpenIff.lean#L243-L270

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

theorem GlobalTheory.exists_isInvariantSection_mem_basicOpen_iff [Finite G] {U : X.Opens}
    (hU : ∀ g, U ≤ (ρ g).hom ⁻¹ᵁ U) (s : Γ(X, U)) :
    ∃ t : Γ(X, U), IsInvariantSection ρ U t ∧
      ∀ x, x ∈ X.basicOpen t ↔ ∀ g, (ρ g).hom x ∈ X.basicOpen s := by sorry
