-- Prove2me | Theorems.Thm_GlobalTheory_lift_unique_of_isDominant
-- name    : GlobalTheory.lift_unique_of_isDominant
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:28:34.336823+00:00
-- url     : https://prove2.me/theorems/46fead37-b4f6-45d2-8d58-bfbfadc2b912
-- title:
--   Global Theory: lift unique of is Dominant
-- statement:
--   The Global Theory construction uses the lift unique of is Dominant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueLiftSpecOfIsLocalizationAway.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueLiftSpecOfIsLocalizationAway.lean#L44-L45

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

theorem GlobalTheory.lift_unique_of_isDominant (j : U ⟶ T) [IsDominant j] [IsReduced T] (p : Z ⟶ Y)
    [IsSeparated p] {c c' : T ⟶ Z} (h₁ : j ≫ c = j ≫ c') (h₂ : c ≫ p = c' ≫ p) : c = c' := by sorry
