-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_eigen_complement_of_adjoint_stable_kernel
-- name    : GlobalTheory.T.exists_eigen_complement_of_adjoint_stable_kernel
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:28:58.957877+00:00
-- url     : https://prove2.me/theorems/9a8081aa-a589-4726-9133-3de5d3169952
-- title:
--   T: exists eigen complement of adjoint stable kernel
-- statement:
--   The T construction uses the exists eigen complement of adjoint stable kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StableComplementOfKernelExistsStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StableComplementOfKernelExistsStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StableComplementOfKernelExists
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StableComplementOfKernelExistsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_eigen_complement_of_adjoint_stable_kernel : ∀ (V W H : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H), Function.Injective ι → ∀ (pr : V →ₗ[ℂ] W) (H0 : Submodule ℂ V), FiniteDimensional ℂ H0 → ∀ (A : Set (Module.End ℂ V)), (∀ a ∈ A, ∀ v ∈ H0, a v ∈ H0) → (∀ a ∈ A, ∀ v ∈ H0, pr v = 0 → pr (a v) = 0) → (∀ a ∈ A, ∃ b ∈ A, ∀ u v, inner ℂ (ι (a u)) (ι v) = inner ℂ (ι u) (ι (b v))) → ∀ h ∈ H0, ∃ c ∈ H0, pr c = pr h ∧ ∀ a ∈ A, ∀ z : ℂ, pr (a c) = z • pr c → a c = z • c := by sorry
