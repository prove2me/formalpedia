-- Prove2me | Theorems.Thm_GlobalTheory_T_tensor_maximalStable_contains_leftKernel
-- name    : GlobalTheory.T.tensor_maximalStable_contains_leftKernel
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:59:33.619941+00:00
-- url     : https://prove2.me/theorems/0071bd82-d5fc-401e-a50b-80dffa8faff9
-- title:
--   T: tensor maximal Stable contains left Kernel
-- statement:
--   The T construction uses the tensor maximal Stable contains left Kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/TensorMaximalStableContainsLeftKernelStatement.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/TensorMaximalStableContainsLeftKernelStatement.lean#L9-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TensorMaximalStableContainsLeftKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeKerOfLocalFiniteLengthToSimpleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TensorMaximalStableContainsLeftKernelStatement
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

theorem GlobalTheory.T.tensor_maximalStable_contains_leftKernel : ∀ {M₀ V : Type} [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup V] [Module ℂ V]
    (Op₀ : Set (Module.End ℂ M₀)) (B : Set (Module.End ℂ V)) (Rel₀ K₀ : Submodule ℂ M₀),
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M₀), StrictMono N →
        (∀ j, Rel₀ ≤ N j ∧ ∀ g ∈ Op₀, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    (∀ N : Submodule ℂ M₀, Rel₀ ≤ N → GlobalTheory.TensHead.Stab Op₀ N → N ≠ ⊤ → N ≤ K₀) →
    K₀ ≠ ⊤ → GlobalTheory.TensHead.Stab Op₀ K₀ →
    ∀ N' : Submodule ℂ (M₀ ⊗[ℂ] V),
      (∀ x ∈ Rel₀, ∀ y, x ⊗ₜ[ℂ] y ∈ N') → GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps Op₀ B) N' →
      (∀ U, GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps Op₀ B) U → N' ≤ U → U = N' ∨ U = ⊤) →
      ∀ x ∈ K₀, ∀ y, x ⊗ₜ[ℂ] y ∈ N' := by sorry
