-- Prove2me | Theorems.Thm_GlobalTheory_IsInvariantSection_basicOpen_le
-- name    : GlobalTheory.IsInvariantSection.basicOpen_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:42:43.056917+00:00
-- url     : https://prove2.me/theorems/cd46b3d2-156a-4e7e-b3d7-862541755bdb
-- title:
--   Is Invariant Section: basic Open le
-- statement:
--   The Is Invariant Section construction uses the basic Open le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsInvariantSectionMemBasicOpenIff.lean#L217-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsInvariantSectionMemBasicOpenIff.lean#L217-L222

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

theorem GlobalTheory.IsInvariantSection.basicOpen_le {U : X.Opens} {s : Γ(X, U)}
    (hs : IsInvariantSection ρ U s) (g : G) : X.basicOpen s ≤ (ρ g).hom ⁻¹ᵁ X.basicOpen s := by sorry
