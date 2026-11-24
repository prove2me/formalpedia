-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_isClosedEmbedding_stepPt
-- name    : GlobalTheory.FunObj.isClosedEmbedding_stepPt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:41:07.148288+00:00
-- url     : https://prove2.me/theorems/f57228a3-20a4-4efa-9c61-14c1a06fd9d1
-- title:
--   Fun Obj: is Closed Embedding step Pt
-- statement:
--   The Fun Obj construction uses the is Closed Embedding step Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L141-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L141-L154

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] {n : Type*} {c : ℕ} {n' : Type*}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.FunObj.isClosedEmbedding_stepPt (x₀ : Matrix n n' k) :
    Topology.IsClosedEmbedding (stepPt x₀ : (StepVar n c n' → k) → _) := by sorry
