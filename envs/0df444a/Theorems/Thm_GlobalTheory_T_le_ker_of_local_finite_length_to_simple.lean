-- Prove2me | Theorems.Thm_GlobalTheory_T_le_ker_of_local_finite_length_to_simple
-- name    : GlobalTheory.T.le_ker_of_local_finite_length_to_simple
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:36.313863+00:00
-- url     : https://prove2.me/theorems/59070d96-6f54-4189-8647-9177882f6ff5
-- title:
--   T: le ker of local finite length to simple
-- statement:
--   The T construction uses the le ker of local finite length to simple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeKerOfLocalFiniteLengthToSimpleStatement.lean#L8-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeKerOfLocalFiniteLengthToSimpleStatement.lean#L8-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeKerOfLocalFiniteLengthToSimple
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeKerOfLocalFiniteLengthToSimpleStatement
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

theorem GlobalTheory.T.le_ker_of_local_finite_length_to_simple : ∀ {M W : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup W] [Module ℂ W]
    (Op : Set (Module.End ℂ M)) (Rel K : Submodule ℂ M) (φ : M →ₗ[ℂ] W)
    (act : Module.End ℂ M → Module.End ℂ W) (B : Set (Module.End ℂ W)),
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    (∀ N : Submodule ℂ M, Rel ≤ N → GlobalTheory.TensHead.Stab Op N → N ≠ ⊤ → N ≤ K) →
    K ≠ ⊤ → GlobalTheory.TensHead.Stab Op K → Rel ≤ LinearMap.ker φ →
    (∀ g ∈ Op, φ ∘ₗ g = act g ∘ₗ φ) →
    (∀ g ∈ Op, ∀ b ∈ B, act g * b = b * act g) →
    (∀ U : Submodule ℂ W, GlobalTheory.TensHead.Stab (act '' Op ∪ B) U → U = ⊥ ∨ U = ⊤) →
    K ≤ LinearMap.ker φ := by sorry
