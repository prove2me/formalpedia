-- Prove2me | Theorems.Thm_GlobalTheory_Nef_FundId_ord_toRing
-- name    : GlobalTheory.Nef.FundId.ord_toRing
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:04:24.931738+00:00
-- url     : https://prove2.me/theorems/aacb2993-7724-4a1a-b2cb-60e20bff6d34
-- title:
--   Fund Id: ord to Ring
-- statement:
--   The Fund Id construction uses the ord to Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceSumOrderEqFinrank.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceSumOrderEqFinrank.lean#L35-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_GroundTheory_FunctionField_PlaceSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceSumOrderEqFinrank
import Theorems.Thm_GlobalTheory_Nef_Lib_ord_toRing

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

theorem GlobalTheory.Nef.FundId.ord_toRing [GroundTheory.FunctionField.IsFunctionField k F] (v : Place k F) (x : F) :
    (toRing v).ord x = ord v x := by sorry
