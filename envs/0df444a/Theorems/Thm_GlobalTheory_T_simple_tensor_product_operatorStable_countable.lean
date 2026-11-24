-- Prove2me | Theorems.Thm_GlobalTheory_T_simple_tensor_product_operatorStable_countable
-- name    : GlobalTheory.T.simple_tensor_product_operatorStable_countable
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:57:34.946071+00:00
-- url     : https://prove2.me/theorems/318e6644-2c4c-42af-a127-684083c7c582
-- title:
--   T: simple tensor product operator Stable countable
-- statement:
--   The T construction uses the simple tensor product operator Stable countable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SimpleTensorProductOperatorStableCountableStatement.lean#L8-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SimpleTensorProductOperatorStableCountableStatement.lean#L8-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleTensorProductOperatorStableCountable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleTensorProductOperatorStableCountableStatement
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

theorem GlobalTheory.T.simple_tensor_product_operatorStable_countable : ∀ {S₀ S₁ : Type} [AddCommGroup S₀] [Module ℂ S₀] [AddCommGroup S₁] [Module ℂ S₁]
    (A : Set (Module.End ℂ S₀)) (B : Set (Module.End ℂ S₁)),
    Module.rank ℂ S₀ ≤ Cardinal.aleph0 →
    (∀ U : Submodule ℂ S₀, GlobalTheory.TensHead.Stab A U → U = ⊥ ∨ U = ⊤) →
    (∀ U : Submodule ℂ S₁, GlobalTheory.TensHead.Stab B U → U = ⊥ ∨ U = ⊤) →
    ∀ U : Submodule ℂ (S₀ ⊗[ℂ] S₁), GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps A B) U → U = ⊥ ∨ U = ⊤ := by sorry
