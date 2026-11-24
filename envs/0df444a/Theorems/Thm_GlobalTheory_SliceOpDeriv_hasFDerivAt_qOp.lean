-- Prove2me | Theorems.Thm_GlobalTheory_SliceOpDeriv_hasFDerivAt_qOp
-- name    : GlobalTheory.SliceOpDeriv.hasFDerivAt_qOp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:14:41.764448+00:00
-- url     : https://prove2.me/theorems/3491cbe7-0a99-4541-9192-7ef9fc3dd314
-- title:
--   Slice Op Deriv: has FDeriv At q Op
-- statement:
--   The Slice Op Deriv construction uses the has FDeriv At q Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PartialOperatorFderivFormula.lean#L129-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PartialOperatorFderivFormula.lean#L129-L141

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SeminormSliceRLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivPdLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PartialOperatorFderivFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.SliceOpDeriv
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']

theorem GlobalTheory.SliceOpDeriv.hasFDerivAt_qOp (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ)
    (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (s : κ ⊕ κ₁' → V) :
    HasFDerivAt (qOp P f)
      (((xPart P f (s ∘ Sum.inl) (s ∘ Sum.inr)).coprod
        (fderiv ℝ (P (sliceR f (s ∘ Sum.inl))) (s ∘ Sum.inr))).comp splitL) s := by sorry
