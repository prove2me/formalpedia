-- Prove2me | Theorems.Thm_GlobalTheory_Nef_OrdCalc_nrm_max
-- name    : GlobalTheory.Nef.OrdCalc.nrm_max
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:59:56.280947+00:00
-- url     : https://prove2.me/theorems/2455cc44-f768-4f07-b2bb-67db39643b74
-- title:
--   Ord Calc: nrm max
-- statement:
--   The Ord Calc construction uses the nrm max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceOrderCalculus.lean#L49-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceOrderCalculus.lean#L49-L60

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

theorem GlobalTheory.Nef.OrdCalc.nrm_max (v : Place k F) (n : ℕ) (x : Fin n → F) (hx : x ≠ 0) :
    ∃ i, x i ≠ 0 ∧ nrm v x = v.1 (x i) ∧ ordVec v x = ord v (x i) ∧ ∀ j, v.1 (x j) ≤ v.1 (x i) := by sorry
