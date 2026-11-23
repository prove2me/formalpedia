-- Prove2me | Theorems.Thm_GlobalTheory_SliceOp_contDiff_qOp
-- name    : GlobalTheory.SliceOp.contDiff_qOp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:50:11.208621+00:00
-- url     : https://prove2.me/theorems/7aec452a-c5f0-4b1e-859d-4e77082acb80
-- title:
--   Slice Op: cont Diff q Op
-- statement:
--   The Slice Op construction uses the cont Diff q Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzTensorRightOperator.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzTensorRightOperator.lean#L35-L37

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

theorem GlobalTheory.SliceOp.contDiff_qOp (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ)
    (f : SchwartzMap (κ ⊕ κ' → V) ℂ) : ContDiff ℝ ∞ (qOp P f) := by sorry
