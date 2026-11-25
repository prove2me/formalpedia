-- Prove2me | Theorems.Thm_GlobalTheory_Nef_FundId_deg_eq_one
-- name    : GlobalTheory.Nef.FundId.deg_eq_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:02:15.854123+00:00
-- url     : https://prove2.me/theorems/4d196621-cb09-45a3-864e-e8ab67e5e80e
-- title:
--   Fund Id: deg eq one
-- statement:
--   The Fund Id construction uses the deg eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceSumOrderEqFinrank.lean#L53-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceSumOrderEqFinrank.lean#L53-L61

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

theorem GlobalTheory.Nef.FundId.deg_eq_one [IsAlgClosed k] [GroundTheory.FunctionField.IsFunctionField k F]
    (w : GroundTheory.FunctionField.Place k F) : w.deg = 1 := by sorry
