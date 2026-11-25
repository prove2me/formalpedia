-- Prove2me | Theorems.Thm_GlobalTheory_Nef_LocalIndex_exists_primitive
-- name    : GlobalTheory.Nef.LocalIndex.exists_primitive
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:48:18.116524+00:00
-- url     : https://prove2.me/theorems/b626bc70-be17-51f5-91d1-eea7638792fc
-- title:
--   Local Index: exists primitive
-- statement:
--   The Local Index construction uses the exists primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceLocalIndexColength.lean#L67-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceLocalIndexColength.lean#L67-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceOrderCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceIsDVRAndResidueEqGroundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceLocalIndexColength
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
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.LocalIndex
open GlobalTheory.Nef.OrdCalc
variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem GlobalTheory.Nef.LocalIndex.exists_primitive (v : Place k F) {n : ℕ} (a : Matrix (Fin n) (Fin n) F) (hd : a.det ≠ 0)
    (hlt : v.1 a.det < 1) :
    ∃ (c : Fin n → F) (i : Fin n), c i = 1 ∧ (∀ l, v.1 (c l) ≤ 1) ∧ ∀ l, v.1 (a.mulVec c l) < 1 := by sorry
