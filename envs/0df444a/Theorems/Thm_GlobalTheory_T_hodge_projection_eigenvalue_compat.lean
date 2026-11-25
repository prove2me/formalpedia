-- Prove2me | Theorems.Thm_GlobalTheory_T_hodge_projection_eigenvalue_compat
-- name    : GlobalTheory.T.hodge_projection_eigenvalue_compat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:32:40.981595+00:00
-- url     : https://prove2.me/theorems/cbef042d-e61d-5f54-8f4a-d1df0c01f5d4
-- title:
--   T: hodge projection eigenvalue compat
-- statement:
--   The T construction uses the hodge projection eigenvalue compat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeProjectionEigenvalueCompatStatement.lean#L5-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeProjectionEigenvalueCompatStatement.lean#L5-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeProjectionEigenvalueCompat
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeProjectionEigenvalueCompatStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hodge_projection_eigenvalue_compat : ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (P : Λ →+ W),
    Submodule.span ℂ (Set.range P) = ⊤ → ∀ (Q : W →ₗ[ℂ] (Fin g → ℂ)), (∀ x, Q (P x) = x) →
    ∀ (O : Type) (T : O → Module.End ℂ W) (χ : O → Fin g → ℂ),
    (∀ a (x : Λ), (fun j ↦ χ a j * (x : Fin g → ℂ) j) ∈ Λ) →
    (∀ a (x y : Λ), (y : Fin g → ℂ) = (fun j ↦ χ a j * (x : Fin g → ℂ) j) → T a (P x) = P y) →
    ∀ ψ : O → ℂ, (∀ j, ∃ a, χ a j ≠ ψ a) →
    (⨅ a, Module.End.eigenspace (T a) (ψ a) : Submodule ℂ W) ≤ LinearMap.ker Q := by sorry
