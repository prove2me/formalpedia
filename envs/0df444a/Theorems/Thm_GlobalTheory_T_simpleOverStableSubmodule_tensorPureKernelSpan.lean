-- Prove2me | Theorems.Thm_GlobalTheory_T_simpleOverStableSubmodule_tensorPureKernelSpan
-- name    : GlobalTheory.T.simpleOverStableSubmodule_tensorPureKernelSpan
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:22:28.386884+00:00
-- url     : https://prove2.me/theorems/423dfc3c-1b61-47e3-a7f2-b9a214694579
-- title:
--   T: simple Over Stable Submodule tensor Pure Kernel Span
-- statement:
--   The T construction uses the simple Over Stable Submodule tensor Pure Kernel Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SimpleOverStableSubmoduleTensorPureKernelSpanStatement.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SimpleOverStableSubmoduleTensorPureKernelSpanStatement.lean#L9-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmoduleTensorPureKernelSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleTensorProductOperatorStableCountableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmoduleTensorPureKernelSpanStatement
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

theorem GlobalTheory.T.simpleOverStableSubmodule_tensorPureKernelSpan : ∀ {V₀ V₁ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
    (A : Set (Module.End ℂ V₀)) (B : Set (Module.End ℂ V₁)) (K₀ : Submodule ℂ V₀) (K₁ : Submodule ℂ V₁),
    Module.rank ℂ V₀ ≤ Cardinal.aleph0 → GlobalTheory.TensHead.Stab A K₀ → GlobalTheory.TensHead.Stab B K₁ →
    GlobalTheory.TensHead.SimpleOver A K₀ → GlobalTheory.TensHead.SimpleOver B K₁ →
    GlobalTheory.TensHead.SimpleOver (GlobalTheory.TensHead.tensOps A B) (GlobalTheory.TensHead.tensKer K₀ K₁) := by sorry
