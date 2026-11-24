-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_stepPt_row
-- name    : GlobalTheory.FunObj.stepPt_row
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:43:50.909748+00:00
-- url     : https://prove2.me/theorems/002e68d8-2f28-44d1-908b-9706c39d80e4
-- title:
--   Fun Obj: step Pt row
-- statement:
--   The Fun Obj construction uses the step Pt row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L134-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L134-L137

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

theorem GlobalTheory.FunObj.stepPt_row (x₀ : Matrix n n' k) (e : StepVar n c n' → k) (s : n') {l : Fin c} (hl : l.val = c / 2) :
    stepPt x₀ e (.inr l) (.inl s) = keptPt (keptPart e) (.inr l) (.inl s) := by sorry
