-- Prove2me | Theorems.Thm_GlobalTheory_Nef_OrdCalc_le_iff
-- name    : GlobalTheory.Nef.OrdCalc.le_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:01:30.605233+00:00
-- url     : https://prove2.me/theorems/c1135f32-8670-4a58-a912-9834fcfd82d0
-- title:
--   Ord Calc: le iff
-- statement:
--   The Ord Calc construction uses the le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceOrderCalculus.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceOrderCalculus.lean#L28-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceOrderCalculus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option autoImplicit false
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.OrdCalc
variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem GlobalTheory.Nef.OrdCalc.le_iff (v : Place k F) (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    v.1 x ≤ v.1 y ↔ ord v y ≤ ord v x := by sorry
