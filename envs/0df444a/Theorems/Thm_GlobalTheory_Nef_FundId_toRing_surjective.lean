-- Prove2me | Theorems.Thm_GlobalTheory_Nef_FundId_toRing_surjective
-- name    : GlobalTheory.Nef.FundId.toRing_surjective
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:01:02.002573+00:00
-- url     : https://prove2.me/theorems/5a945370-1993-41b7-af25-bd7dcd01f060
-- title:
--   Fund Id: to Ring surjective
-- statement:
--   The Fund Id construction uses the to Ring surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceSumOrderEqFinrank.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceSumOrderEqFinrank.lean#L45-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_GroundTheory_FunctionField_PlaceSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceSumOrderEqFinrank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.FundId
variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem GlobalTheory.Nef.FundId.toRing_surjective [GroundTheory.FunctionField.IsFunctionField k F] :
    Function.Surjective (toRing : Place k F → _) := by sorry
