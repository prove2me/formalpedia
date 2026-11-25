-- Prove2me | Theorems.Thm_GlobalTheory_Nef_FundId_toRing_injective
-- name    : GlobalTheory.Nef.FundId.toRing_injective
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:01:58.582903+00:00
-- url     : https://prove2.me/theorems/99727e6a-934d-4001-888b-54c35ccc0df6
-- title:
--   Fund Id: to Ring injective
-- statement:
--   The Fund Id construction uses the to Ring injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceSumOrderEqFinrank.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceSumOrderEqFinrank.lean#L41-L43

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

theorem GlobalTheory.Nef.FundId.toRing_injective [GroundTheory.FunctionField.IsFunctionField k F] :
    Function.Injective (toRing : Place k F → _) := by sorry
