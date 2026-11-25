-- Prove2me | Theorems.Thm_GlobalTheory_PiSimple_simpleOver_piKer
-- name    : GlobalTheory.PiSimple.simpleOver_piKer
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:04:19.569669+00:00
-- url     : https://prove2.me/theorems/d2a555b9-68dd-4ac1-87dd-0312bc007a47
-- title:
--   Pi Simple: simple Over pi Ker
-- statement:
--   The Pi Simple construction uses the simple Over pi Ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SimpleOverStableSubmodulePiTensor.lean#L220-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SimpleOverStableSubmodulePiTensor.lean#L220-L227

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

theorem GlobalTheory.PiSimple.simpleOver_piKer : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (Op : ∀ i, Set (Module.End ℂ (M i)))
    (K : ∀ i, Submodule ℂ (M i)),
    (∀ i, Module.rank ℂ (M i) ≤ Cardinal.aleph0) → (∀ i, GlobalTheory.TensHead.Stab (Op i) (K i)) →
    (∀ i, GlobalTheory.TensHead.SimpleOver (Op i) (K i)) →
    GlobalTheory.TensHead.SimpleOver (GlobalTheory.TensHead.piOps Op) (GlobalTheory.TensHead.piKer K) := by sorry
