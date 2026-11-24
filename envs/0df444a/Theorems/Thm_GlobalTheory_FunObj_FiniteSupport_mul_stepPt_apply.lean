-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_mul_stepPt_apply
-- name    : GlobalTheory.FunObj.FiniteSupport.mul_stepPt_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:43:00.305031+00:00
-- url     : https://prove2.me/theorems/50660876-2e09-4eb2-bcbb-3b6b089069fb
-- title:
--   Finite Support: mul step Pt apply
-- statement:
--   The Finite Support construction uses the mul step Pt apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteUnfSupportOfNeOne.lean#L41-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteUnfSupportOfNeOne.lean#L41-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteUnfSupportOfNeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.FiniteSupport
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.RootEx.Supp GlobalTheory.RootEx.FJUnipotent
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [Fintype n'] [DecidableEq n']

theorem GlobalTheory.FunObj.FiniteSupport.mul_stepPt_apply {b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (hb : b.BlockTriangular (midLev (c / 2)))
    (x₀ : Matrix n n' k) (e : StepVar n c n' → k) (r : n ⊕ Fin c) (j : Fin c)
    (h : symLev c r = symLev c (Sum.inr j : n ⊕ Fin c)) :
    (b * stepPt x₀ e) r (Sum.inr j.castSucc) = b r (Sum.inr j) := by sorry
