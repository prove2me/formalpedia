-- Prove2me | Theorems.Thm_GlobalTheory_SliceOp_decay_qOp
-- name    : GlobalTheory.SliceOp.decay_qOp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:15:51.785182+00:00
-- url     : https://prove2.me/theorems/a174208b-393d-41cb-9817-24d85df8fb25
-- title:
--   Slice Op: decay q Op
-- statement:
--   The Slice Op construction uses the decay q Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzTensorRightOperator.lean#L39-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzTensorRightOperator.lean#L39-L92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PartialOperatorFderivFormulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PartialOperatorSchwartzSeminormBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivativeBoundByPartialsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTensorRightOperator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SliceSchwartz
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.SliceOp
open GlobalTheory.SliceSchwartz
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']

theorem GlobalTheory.SliceOp.decay_qOp (n : ℕ) : ∀ (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (k : ℕ),
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (z : κ ⊕ κ₁' → V),
      ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (qOp P f) z‖ ≤ C * s.sup (schwartzSeminormFamily ℂ (κ ⊕ κ' → V) ℂ) f := by sorry
