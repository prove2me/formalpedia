-- Prove2me | Theorems.Thm_GlobalTheory_isIntegrallyClosedIn_of_injective_fractionRing
-- name    : GlobalTheory.isIntegrallyClosedIn_of_injective_fractionRing
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:58:31.424798+00:00
-- url     : https://prove2.me/theorems/d174da2b-aa50-4bca-a895-1462fef97fff
-- title:
--   Global Theory: is Integrally Closed In of injective fraction Ring
-- statement:
--   The Global Theory construction uses the is Integrally Closed In of injective fraction Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueLiftSpecOfIsLocalizationAway.lean#L223-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueLiftSpecOfIsLocalizationAway.lean#L223-L228

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueLiftSpecOfIsLocalizationAway
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory

theorem GlobalTheory.isIntegrallyClosedIn_of_injective_fractionRing (R R' K : Type*) [CommRing R] [CommRing R']
    [CommRing K] [Algebra R R'] [Algebra R K] [Algebra R' K] [IsScalarTower R R' K]
    [IsFractionRing R K] [IsIntegrallyClosed R] (hK : Function.Injective (algebraMap R' K)) :
    IsIntegrallyClosedIn R R' := by sorry
