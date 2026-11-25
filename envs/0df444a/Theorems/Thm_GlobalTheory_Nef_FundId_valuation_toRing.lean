-- Prove2me | Theorems.Thm_GlobalTheory_Nef_FundId_valuation_toRing
-- name    : GlobalTheory.Nef.FundId.valuation_toRing
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:59:19.613917+00:00
-- url     : https://prove2.me/theorems/bd64c6b8-4240-4c61-9bf6-60c99f8c5728
-- title:
--   Fund Id: valuation to Ring
-- statement:
--   The Fund Id construction uses the valuation to Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceSumOrderEqFinrank.lean#L28-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceSumOrderEqFinrank.lean#L28-L33

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

theorem GlobalTheory.Nef.FundId.valuation_toRing [GroundTheory.FunctionField.IsFunctionField k F] (v : Place k F) :
    (toRing v).valuation = v.1 := by sorry
