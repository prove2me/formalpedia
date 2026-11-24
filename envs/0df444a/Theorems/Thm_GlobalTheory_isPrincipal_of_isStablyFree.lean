-- Prove2me | Theorems.Thm_GlobalTheory_isPrincipal_of_isStablyFree
-- name    : GlobalTheory.isPrincipal_of_isStablyFree
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:59:30.289643+00:00
-- url     : https://prove2.me/theorems/f88271af-f2f8-4a70-84f5-f6f58e47a792
-- title:
--   Global Theory: is Principal of is Stably Free
-- statement:
--   The Global Theory construction uses the is Principal of is Stably Free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsPrincipalMapAwayOfHasProjectiveDimensionLE.lean#L73-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsPrincipalMapAwayOfHasProjectiveDimensionLE.lean#L73-L96

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsPrincipalMapAwayOfHasProjectiveDimensionLE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open scoped TensorProduct

theorem GlobalTheory.isPrincipal_of_isStablyFree {A : Type} [CommRing A] (J : Ideal A) [Module.Finite A J]
    [Module.IsStablyFree A J] : J.IsPrincipal := by sorry
