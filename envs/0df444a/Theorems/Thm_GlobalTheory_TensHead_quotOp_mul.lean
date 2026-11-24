-- Prove2me | Theorems.Thm_GlobalTheory_TensHead_quotOp_mul
-- name    : GlobalTheory.TensHead.quotOp_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:02:22.035693+00:00
-- url     : https://prove2.me/theorems/02276683-a3e9-4e24-a6db-dc04577a6985
-- title:
--   Tens Head: quot Op mul
-- statement:
--   The Tens Head construction uses the quot Op mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PiTensorMaximalStableContainsFactorKernel.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PiTensorMaximalStableContainsFactorKernel.lean#L24-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeKerOfLocalFiniteLengthToSimpleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EqTopOfPureTensorsOfFactorGenerators
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PiTensorMaximalStableContainsFactorKernel
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
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.TensHead.quotOp_mul (N : Submodule ℂ V) (f₁ f₂ : Module.End ℂ V) (h₁ : ∀ x ∈ N, f₁ x ∈ N)
    (h₂ : ∀ x ∈ N, f₂ x ∈ N) : quotOp N f₁ * quotOp N f₂ = quotOp N (f₁ * f₂) := by sorry
