-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_exists_unit_bd
-- name    : GlobalTheory.FunObj.FiniteSupport.exists_unit_bd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:40:52.98361+00:00
-- url     : https://prove2.me/theorems/676a8842-0b0c-47e0-b59a-e7d6523010b8
-- title:
--   Finite Support: exists unit bd
-- statement:
--   The Finite Support construction uses the exists unit bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteUnfSupportOfNeOne.lean#L360-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteUnfSupportOfNeOne.lean#L360-L370

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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.FunObj.FiniteSupport.exists_unit_bd {ι : Type} [Fintype ι] [DecidableEq ι] {S : Set (GL ι k)} (hS : S.Finite) :
    ∃ s : kˣ, ∀ g ∈ S, Bd (valuation k (s : k)) g.val ∧ Bd (valuation k (s : k)) (g⁻¹).val := by sorry
