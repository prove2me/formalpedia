-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_lift_of_isOpenImmersion_of_isDominant
-- name    : GlobalTheory.existsUnique_lift_of_isOpenImmersion_of_isDominant
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:29:11.875519+00:00
-- url     : https://prove2.me/theorems/5842470a-5d22-453a-afcc-139f2aacbe1a
-- title:
--   Global Theory: exists Unique lift of is Open Immersion of is Dominant
-- statement:
--   The Global Theory construction uses the exists Unique lift of is Open Immersion of is Dominant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueLiftSpecOfIsLocalizationAway.lean#L103-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueLiftSpecOfIsLocalizationAway.lean#L103-L173

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

theorem GlobalTheory.existsUnique_lift_of_isOpenImmersion_of_isDominant (j : U ⟶ T) [IsOpenImmersion j]
    [IsDominant j] [IsNormalScheme T] [IsLocallyNoetherian T]
    (p : Z ⟶ Y) [IsIntegralHom p] (a : U ⟶ Z) (b : T ⟶ Y) (h : a ≫ p = j ≫ b) :
    ∃! c : T ⟶ Z, j ≫ c = a ∧ c ≫ p = b := by sorry
