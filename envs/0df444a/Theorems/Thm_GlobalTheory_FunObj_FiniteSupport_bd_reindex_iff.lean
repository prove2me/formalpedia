-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_bd_reindex_iff
-- name    : GlobalTheory.FunObj.FiniteSupport.bd_reindex_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:40:54.314748+00:00
-- url     : https://prove2.me/theorems/d77c41fa-8b6c-42f1-9e5f-5db3d6178948
-- title:
--   Finite Support: bd reindex iff
-- statement:
--   The Finite Support construction uses the bd reindex iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteUnfSupportOfNeOne.lean#L231-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteUnfSupportOfNeOne.lean#L231-L233

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
variable [ValuativeRel k]

theorem GlobalTheory.FunObj.FiniteSupport.bd_reindex_iff {ι κ ι' κ' : Type} {γ : ValueGroupWithZero k} {x : Matrix ι κ k} (f : ι ≃ ι')
    (g : κ ≃ κ') : Bd γ (x.reindex f g) ↔ Bd γ x := by sorry
