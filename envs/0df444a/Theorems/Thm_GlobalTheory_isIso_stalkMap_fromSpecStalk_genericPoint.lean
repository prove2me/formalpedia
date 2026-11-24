-- Prove2me | Theorems.Thm_GlobalTheory_isIso_stalkMap_fromSpecStalk_genericPoint
-- name    : GlobalTheory.isIso_stalkMap_fromSpecStalk_genericPoint
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:57:53.363446+00:00
-- url     : https://prove2.me/theorems/55571494-1627-40f9-b582-10e93319cba1
-- title:
--   Global Theory: is Iso stalk Map from Spec Stalk generic Point
-- statement:
--   The Global Theory construction uses the is Iso stalk Map from Spec Stalk generic Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueLiftSpecOfIsLocalizationAway.lean#L56-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueLiftSpecOfIsLocalizationAway.lean#L56-L70

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
variable {U T Z Y : Scheme.{u}}

theorem GlobalTheory.isIso_stalkMap_fromSpecStalk_genericPoint (U : Scheme.{u}) [IsIntegral U] :
    IsIso ((U.fromSpecStalk (genericPoint U)).stalkMap (genericPoint _)) := by sorry
