-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_frameGL_symm_val
-- name    : GlobalTheory.FunObj.FiniteSupport.frameGL_symm_val
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:05:58.577304+00:00
-- url     : https://prove2.me/theorems/154dd0c5-618c-5878-998f-dba13ca79235
-- title:
--   Finite Support: frame GL symm val
-- statement:
--   The Finite Support construction uses the frame GL symm val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteUnfSupportOfNeOne.lean#L213-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteUnfSupportOfNeOne.lean#L213-L214

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
variable {k : Type} [Field k] {a c b : ℕ}

theorem GlobalTheory.FunObj.FiniteSupport.frameGL_symm_val (h : a + c = b) (g : GL (Fin a ⊕ Fin c) k) :
    ((frameGL h).symm g).val = g.val.submatrix (frame h).symm (frame h).symm := by sorry
