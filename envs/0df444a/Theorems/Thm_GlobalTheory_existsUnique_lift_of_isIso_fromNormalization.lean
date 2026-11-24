-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_lift_of_isIso_fromNormalization
-- name    : GlobalTheory.existsUnique_lift_of_isIso_fromNormalization
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:27:40.568592+00:00
-- url     : https://prove2.me/theorems/c2b04f07-ab5c-462d-9829-de7ffe0e98dd
-- title:
--   Global Theory: exists Unique lift of is Iso from Normalization
-- statement:
--   The Global Theory construction uses the exists Unique lift of is Iso from Normalization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueLiftSpecOfIsLocalizationAway.lean#L15-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueLiftSpecOfIsLocalizationAway.lean#L15-L42

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

theorem GlobalTheory.existsUnique_lift_of_isIso_fromNormalization (j : U ⟶ T) [QuasiCompact j]
    [QuasiSeparated j] [IsIso j.fromNormalization] (p : Z ⟶ Y) [IsIntegralHom p]
    (a : U ⟶ Z) (b : T ⟶ Y) (h : a ≫ p = j ≫ b) :
    ∃! c : T ⟶ Z, j ≫ c = a ∧ c ≫ p = b := by sorry
