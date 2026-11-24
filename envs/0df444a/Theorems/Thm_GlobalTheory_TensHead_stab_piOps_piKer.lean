-- Prove2me | Theorems.Thm_GlobalTheory_TensHead_stab_piOps_piKer
-- name    : GlobalTheory.TensHead.stab_piOps_piKer
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:02:37.412782+00:00
-- url     : https://prove2.me/theorems/a2a1c40a-41d0-4769-8df1-14dcf42dc7d8
-- title:
--   Tens Head: stab pi Ops pi Ker
-- statement:
--   The Tens Head construction uses the stab pi Ops pi Ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/OperatorStablePiTensorPureKernelSpan.lean#L10-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/OperatorStablePiTensorPureKernelSpan.lean#L10-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OperatorStablePiTensorPureKernelSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.TensHead
open scoped TensorProduct

theorem GlobalTheory.TensHead.stab_piOps_piKer {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)]
    (Op : ∀ i, Set (Module.End ℂ (M i))) (K : ∀ i, Submodule ℂ (M i))
    (h : ∀ i, _root_.GlobalTheory.TensHead.Stab (Op i) (K i)) :
    _root_.GlobalTheory.TensHead.Stab (_root_.GlobalTheory.TensHead.piOps Op) (_root_.GlobalTheory.TensHead.piKer K) := by sorry
