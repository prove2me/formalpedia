-- Prove2me | Theorems.Thm_GlobalTheory_isIso_fromNormalization_spec_of_isIntegrallyClosedIn
-- name    : GlobalTheory.isIso_fromNormalization_spec_of_isIntegrallyClosedIn
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:57:16.53665+00:00
-- url     : https://prove2.me/theorems/4f9b6715-05c6-49b6-a75e-1ddb386099c7
-- title:
--   Global Theory: is Iso from Normalization spec of is Integrally Closed In
-- statement:
--   The Global Theory construction uses the is Iso from Normalization spec of is Integrally Closed In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueLiftSpecOfIsLocalizationAway.lean#L179-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueLiftSpecOfIsLocalizationAway.lean#L179-L221

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

theorem GlobalTheory.isIso_fromNormalization_spec_of_isIntegrallyClosedIn (R R' : Type u) [CommRing R]
    [CommRing R'] [Algebra R R'] [IsIntegrallyClosedIn R R'] :
    IsIso (Spec.map (CommRingCat.ofHom (algebraMap R R'))).fromNormalization := by sorry
