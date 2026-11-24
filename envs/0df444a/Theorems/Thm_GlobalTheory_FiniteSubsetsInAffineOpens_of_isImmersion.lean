-- Prove2me | Theorems.Thm_GlobalTheory_FiniteSubsetsInAffineOpens_of_isImmersion
-- name    : GlobalTheory.FiniteSubsetsInAffineOpens.of_isImmersion
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:42:18.138109+00:00
-- url     : https://prove2.me/theorems/42a9aa52-47d2-4e22-af2c-0012cb7160bc
-- title:
--   Finite Subsets In Affine Opens: of is Immersion
-- statement:
--   The Finite Subsets In Affine Opens construction uses the of is Immersion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsInvariantSectionMemBasicOpenIff.lean#L84-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsInvariantSectionMemBasicOpenIff.lean#L84-L86

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

theorem GlobalTheory.FiniteSubsetsInAffineOpens.of_isImmersion (f : X ⟶ Y) [IsImmersion f] [FiniteSubsetsInAffineOpens Y] :
    FiniteSubsetsInAffineOpens X := by sorry
