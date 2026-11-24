-- Prove2me | Theorems.Thm_GlobalTheory_isDominant_fromSpecStalk_genericPoint
-- name    : GlobalTheory.isDominant_fromSpecStalk_genericPoint
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:28:25.773394+00:00
-- url     : https://prove2.me/theorems/98f1c767-8836-4f9c-a648-a889357fb9c3
-- title:
--   Global Theory: is Dominant from Spec Stalk generic Point
-- statement:
--   The Global Theory construction uses the is Dominant from Spec Stalk generic Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueLiftSpecOfIsLocalizationAway.lean#L47-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueLiftSpecOfIsLocalizationAway.lean#L47-L54

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

theorem GlobalTheory.isDominant_fromSpecStalk_genericPoint (U : Scheme.{u}) [IsIntegral U] :
    IsDominant (U.fromSpecStalk (genericPoint U)) := by sorry
