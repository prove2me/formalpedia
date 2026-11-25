-- Prove2me | Theorems.Thm_GlobalTheory_Nef_OrdCalc_nrm_mulVec_le
-- name    : GlobalTheory.Nef.OrdCalc.nrm_mulVec_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:01:13.651215+00:00
-- url     : https://prove2.me/theorems/e1aeb492-b040-4eca-b9c0-0dcbc1d2e15a
-- title:
--   Ord Calc: nrm mul Vec le
-- statement:
--   The Ord Calc construction uses the nrm mul Vec le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceOrderCalculus.lean#L76-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceOrderCalculus.lean#L76-L86

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

theorem GlobalTheory.Nef.OrdCalc.nrm_mulVec_le (v : Place k F) (n : ℕ) (u : Matrix (Fin n) (Fin n) F) (x : Fin n → F)
    (hu : ∀ i j, v.1 (u i j) ≤ 1) : nrm v (u.mulVec x) ≤ nrm v x := by sorry
