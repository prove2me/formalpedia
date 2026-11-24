-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_transpose_mem_matLat
-- name    : GlobalTheory.FunObj.FiniteSupport.transpose_mem_matLat
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:43:04.03881+00:00
-- url     : https://prove2.me/theorems/75fc0d98-5335-4065-a7af-91a385ae5e16
-- title:
--   Finite Support: transpose mem mat Lat
-- statement:
--   The Finite Support construction uses the transpose mem mat Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteUnfSupportOfNeOne.lean#L235-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteUnfSupportOfNeOne.lean#L235-L238

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

theorem GlobalTheory.FunObj.FiniteSupport.transpose_mem_matLat [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι κ : Type} (u : kˣ) {x : Matrix κ ι k} (hx : Bd (valuation k (u : k)) x) :
    xᵀ ∈ matLat ι (u • stdLat k κ) := by sorry
