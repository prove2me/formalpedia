-- Prove2me | Theorems.Thm_GlobalTheory_T_operatorStable_piTensorPureKernelSpan
-- name    : GlobalTheory.T.operatorStable_piTensorPureKernelSpan
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:22:38.066525+00:00
-- url     : https://prove2.me/theorems/ba0f9c94-e3af-4740-8b7b-d37e86932dbb
-- title:
--   T: operator Stable pi Tensor Pure Kernel Span
-- statement:
--   The T construction uses the operator Stable pi Tensor Pure Kernel Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/OperatorStablePiTensorPureKernelSpanStatement.lean#L8-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/OperatorStablePiTensorPureKernelSpanStatement.lean#L8-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OperatorStablePiTensorPureKernelSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OperatorStablePiTensorPureKernelSpanStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.operatorStable_piTensorPureKernelSpan : ∀ {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (Op : ∀ i, Set (Module.End ℂ (M i))) (K : ∀ i, Submodule ℂ (M i)),
    (∀ i, GlobalTheory.TensHead.Stab (Op i) (K i)) →
    GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.piOps Op) (GlobalTheory.TensHead.piKer K) := by sorry
