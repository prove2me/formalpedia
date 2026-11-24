-- Prove2me | Theorems.Thm_GlobalTheory_isIntegrallyClosedIn_of_isLocalization
-- name    : GlobalTheory.isIntegrallyClosedIn_of_isLocalization
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:57:07.932697+00:00
-- url     : https://prove2.me/theorems/bada2b8a-e9ab-4a40-9d25-c7f5ebf87961
-- title:
--   Global Theory: is Integrally Closed In of is Localization
-- statement:
--   The Global Theory construction uses the is Integrally Closed In of is Localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueLiftSpecOfIsLocalizationAway.lean#L230-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueLiftSpecOfIsLocalizationAway.lean#L230-L247

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

theorem GlobalTheory.isIntegrallyClosedIn_of_isLocalization {R : Type*} [CommRing R] [IsIntegrallyClosed R]
    (M : Submonoid R) (hM : M ≤ nonZeroDivisors R) (R' : Type*) [CommRing R'] [Algebra R R']
    [IsLocalization M R'] : IsIntegrallyClosedIn R R' := by sorry
