-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_stepPt_col
-- name    : GlobalTheory.FunObj.stepPt_col
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:04:34.464138+00:00
-- url     : https://prove2.me/theorems/b77b3859-a77d-4ab5-92e0-05bc62228b8b
-- title:
--   Fun Obj: step Pt col
-- statement:
--   The Fun Obj construction uses the step Pt col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L129-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L129-L132

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

theorem GlobalTheory.FunObj.stepPt_col (x₀ : Matrix n n' k) (e : StepVar n c n' → k) (r : n) {i : Fin (c + 1)} (hi : i.val = c / 2) :
    stepPt x₀ e (.inl r) (.inr i) = keptPt (keptPart e) (.inl r) (.inr i) := by sorry
