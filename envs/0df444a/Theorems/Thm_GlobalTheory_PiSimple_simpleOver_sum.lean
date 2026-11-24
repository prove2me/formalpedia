-- Prove2me | Theorems.Thm_GlobalTheory_PiSimple_simpleOver_sum
-- name    : GlobalTheory.PiSimple.simpleOver_sum
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:48:53.629697+00:00
-- url     : https://prove2.me/theorems/cf35a1a2-08d1-484a-affc-a0bb8eda3a43
-- title:
--   Pi Simple: simple Over sum
-- statement:
--   The Pi Simple construction uses the simple Over sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SimpleOverStableSubmodulePiTensor.lean#L102-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SimpleOverStableSubmodulePiTensor.lean#L102-L204

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmoduleTensorPureKernelSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OperatorStablePiTensorPureKernelSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmodulePiTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.PiSimple
open GlobalTheory.TensHead

theorem GlobalTheory.PiSimple.simpleOver_sum {α β : Type} (hα : PP α) (hβ : PP β) [DecidableEq (α ⊕ β)]
    (N : α ⊕ β → Type) [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)]
    (Op : ∀ i, Set (Module.End ℂ (N i))) (K : ∀ i, Submodule ℂ (N i))
    (hr : ∀ i, Module.rank ℂ (N i) ≤ Cardinal.aleph0)
    (hrl : Module.rank ℂ (⨂[ℂ] a, N (.inl a)) ≤ Cardinal.aleph0)
    (hs : ∀ i, Stab (Op i) (K i)) (hso : ∀ i, SimpleOver (Op i) (K i)) :
    SimpleOver (piOps Op) (piKer K) := by sorry
