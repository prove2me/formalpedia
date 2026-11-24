-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_lift_of_birational
-- name    : GlobalTheory.existsUnique_lift_of_birational
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:30:07.91664+00:00
-- url     : https://prove2.me/theorems/6aae320c-c131-48e9-a68d-64351d240742
-- title:
--   Global Theory: exists Unique lift of birational
-- statement:
--   The Global Theory construction uses the exists Unique lift of birational property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueLiftSpecOfIsLocalizationAway.lean#L72-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueLiftSpecOfIsLocalizationAway.lean#L72-L101

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

theorem GlobalTheory.existsUnique_lift_of_birational (j : U ⟶ T) [IsIntegral U] [IsIntegral T]
    [IsNormalScheme T] [IsDominant j] [IsIso (j.stalkMap (genericPoint U))]
    (p : Z ⟶ Y) [IsIntegralHom p] (a : U ⟶ Z) (b : T ⟶ Y) (h : a ≫ p = j ≫ b) :
    ∃! c : T ⟶ Z, j ≫ c = a ∧ c ≫ p = b := by sorry
